
/*--------------------------------------------------------------------*/
/*--- Profilergrind: The better callgrind tool.          sp_main.c ---*/
/*--------------------------------------------------------------------*/

#include "libvex_ir.h"
#include "pub_tool_basics.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_machine.h"
#include "pub_tool_options.h"
#include "pub_tool_stacktrace.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_vki.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_libcproc.h"
#include "pub_tool_debuginfo.h"

#include "m_debuginfo/priv_storage.h" // full _DebugInfo

static const HChar* clo_profilergrind_out_file = "profile.%p.json";
static VgFile* fp = NULL;
static HChar const* sp_dump_filename = NULL;

static HChar const* sp_basename(HChar const* name)
{
   HChar const* p;
   p = VG_(strrchr)(name, '/');
   if (!p)
      p = name;
   else
      p++;
   return p;
}

static void sp_post_clo_init(void)
{
   HChar* out_file =
      VG_(expand_file_name)("--profilergrind-out-file", clo_profilergrind_out_file);

   fp = VG_(fopen)(out_file, VKI_O_CREAT|VKI_O_TRUNC|VKI_O_WRONLY,
                   VKI_S_IRUSR|VKI_S_IWUSR);

   if (fp == NULL) {
      VG_(umsg)("Error: Cannot open output data file '%s'\n", out_file);
      VG_(umsg)("       ... so no profile can be written.\n");
      VG_(free)(out_file);
      return;
   }

   sp_dump_filename = out_file;
   VG_(fprintf)(fp, "{\"strings\": [], \"events\": [\n");
}

#define MAX_STACK_TRACE_DEPTH (1024)
#define MAX_THREAD_COUNT (1024)

static Addr sp_ips[MAX_STACK_TRACE_DEPTH * MAX_THREAD_COUNT] = {0};
static UInt s_millisecond_sample_resolution = 10; // Sample only after at least Nms have passed.
static UInt s_millisecond_sample_last = 0; // Last time we sampled.
static Bool s_first_event = True;


static void sp_sample(Addr* ips, SizeT n_ips)
{
   UInt time = VG_(read_millisecond_timer)();
   if (time - s_millisecond_sample_last < s_millisecond_sample_resolution)
      return;

   s_millisecond_sample_last = time;

   if (s_first_event)
      s_first_event = False;
   else
      VG_(fprintf)(fp, ",\n");

   VG_(fprintf)(fp, "{\"type\": \"sample\", \"pid\": %d, \"tid\": %u, \"timestamp\": %u, \"lost_samples\": %d, \"stack\": [",
                VG_(getpid)(),
                VG_(get_running_tid)(),
                time,
                0);

   for (SizeT i = 0; i < n_ips; i++) {
      if (i > 0)
         VG_(fprintf)(fp, ", ");
      VG_(fprintf)(fp, "%lu", ips[i]);
   }

   VG_(fprintf)(fp, "]}");
}

static
IRSB* sp_instrument ( VgCallbackClosure* closure,
                      IRSB* bb,
                      const VexGuestLayout* layout,
                      const VexGuestExtents* vge,
                      const VexArchInfo* archinfo_host,
                      IRType gWordTy, IRType hWordTy )
{
   // Insert the following at the start of the block:
   //    - call VG_(get_running_tid) -> tid
   //    - call VG_(get_StackTrace)(tid, sp_ips, 64, NULL, NULL, 0) -> n_ips
   //    - call sp_sample(ips, n_ips)

   IRSB* newbb = deepCopyIRSBExceptStmts(bb);
   IRDirty* di;
   IRExpr** args;
   IRStmt* st;
   IRTemp tmp0 = newIRTemp(newbb->tyenv, Ity_I64);
   IRTemp tmp1 = newIRTemp(newbb->tyenv, integerIRTypeOfSize(VG_WORDSIZE));
   IRTemp tmp2 = newIRTemp(newbb->tyenv, integerIRTypeOfSize(VG_WORDSIZE));
   IRTemp tmp3 = newIRTemp(newbb->tyenv, integerIRTypeOfSize(VG_WORDSIZE));

   // Get the tid
   di = unsafeIRDirty_1_N(tmp0, 0, "VG_(get_running_tid)", VG_(get_running_tid), mkIRExprVec_0());
   st = IRStmt_Dirty(di);
   addStmtToIRSB(newbb, st);

   // Resolve ips = sp_ips + (tid * 64)
   IRExpr* ips_offset = IRExpr_Binop(
      Iop_Mul64,
      IRExpr_RdTmp(tmp0),
      IRExpr_Const(IRConst_U64(64)));
   st = IRStmt_WrTmp(tmp2, ips_offset);
   addStmtToIRSB(newbb, st);

   IRExpr* ips = IRExpr_Binop(
      Iop_Add64,
      IRExpr_RdTmp(tmp2),
      IRExpr_Const(IRConst_U64((UWord)sp_ips)));
   st = IRStmt_WrTmp(tmp1, ips);
   addStmtToIRSB(newbb, st);

   // Call VG_(get_StackTrace)(tid, ips, 64, NULL, NULL, 0) -> n_ips
   args = mkIRExprVec_6(
      /* tid = tmp0    */ IRExpr_RdTmp(tmp0),
      /* ips = tmp1    */ IRExpr_RdTmp(tmp1),
      /* count = max   */ mkIRExpr_HWord(MAX_STACK_TRACE_DEPTH),
      /* NULL          */ mkIRExpr_HWord(0),
      /* NULL          */ mkIRExpr_HWord(0),
      /* offset = 0    */ mkIRExpr_HWord(0));

   di = unsafeIRDirty_1_N(tmp3, 0, "VG_(get_StackTrace)", VG_(get_StackTrace), args);
   st = IRStmt_Dirty(di);
   addStmtToIRSB(newbb, st);

   // Call sp_sample(ips, n_ips)
   args = mkIRExprVec_2(IRExpr_RdTmp(tmp1),
                        IRExpr_RdTmp(tmp3));

   di = unsafeIRDirty_0_N(0, "sp_sample", VG_(fnptr_to_fnentry)(sp_sample), args);
   st = IRStmt_Dirty(di);
   addStmtToIRSB(newbb, st);

   // Add the original statements
   for (int i = 0; i < bb->stmts_used; i++)
      addStmtToIRSB(newbb, bb->stmts[i]);

   return newbb;
}

static void sp_fini(Int exitcode)
{
   if (fp != NULL) {
      VG_(fprintf)(fp, "]}\n");
      VG_(fclose)(fp);

      Int pid = VG_(getpid)();
      VG_(umsg)("Reference pack: cp %s pack.%d/profile\n", sp_dump_filename, pid);
      VG_(umsg)("Reference pack: tar -czf pack.%d.tar.gz pack.%d\n", pid, pid);
   }
}

struct Range {
     Addr start;
     SizeT size;
};

static Bool s_is_first_file = True;
static XArray *s_initial_main_exec_ranges = NULL;
static HChar const* sp_dump_di_handle_name(Addr a, SizeT size, ULong di_handle)
{
   HChar const* filename = NULL;
   HChar const* fullname = NULL;

   DebugInfo const* debug_info = NULL;
   do {
      debug_info = VG_(next_DebugInfo(debug_info));
      if (!debug_info)
         break;

      struct _DebugInfo const* di = (struct _DebugInfo const*)debug_info;

      Addr base;
      SizeT size;

#define CHECK(x) \
      base = di->x##_avma; \
      size = di->x##_size; \
      if (a >= base && a < base + size) \
         break;

      CHECK(text);
      CHECK(data);
      CHECK(sdata);
      CHECK(rodata);
      CHECK(sbss);
      CHECK(exidx);
      CHECK(extab);
      CHECK(plt);
      CHECK(got);
      CHECK(gotplt);
      CHECK(opd);

#undef CHECK

      if (di->handle == di_handle) {
         fullname = VG_(DebugInfo_get_filename)(debug_info);
         if (fullname != NULL)
            break;
      }
   } while (1);

   if (debug_info == NULL) {
      // We haven't seen a new file yet, so everything so far is just the next object.
      if (s_initial_main_exec_ranges == NULL)
         s_initial_main_exec_ranges = VG_(newXA)(VG_(malloc), "sp_dump_di_handle_name.initial_main_exec_ranges", VG_(free), sizeof(struct Range));
      struct Range r;
      r.start = a;
      r.size = size;
      VG_(addToXA)(s_initial_main_exec_ranges, &r);

      return NULL;
   }

   fullname = VG_(DebugInfo_get_filename)(debug_info);
   filename = sp_basename(fullname);

   HChar const* so = VG_(strstr)(filename, ".so");
   Int pid = VG_(getpid)();
   if (s_is_first_file) {
      s_is_first_file = False;
      VG_(umsg("Reference dir : mkdir -p pack.%d/usr/lib\n", pid));
   }

   if (so != NULL && (so[3] == 0 || so[3] == '.')) {
      // Shared object
      VG_(umsg)("Reference file: cp %s pack.%d/usr/lib/%s\n", fullname, pid, filename);
   } else {
      // Normal object
      VG_(umsg)("Reference file: cp %s pack.%d/%s\n", fullname, pid, filename);
   }

   return filename;
}

static Bool s_have_seen_executable = False;
static void sp_track_new_mem_mmap(Addr a, SizeT len, Bool rr, Bool ww, Bool xx, ULong di_handle)
{
   HChar const* filename = sp_dump_di_handle_name(a, len, di_handle);

   if (!s_have_seen_executable && filename != NULL) {
      // process_create{pid, parent_pid=pid, executable=filename, tid, timestamp, lost_samples=0, stack=[]}
      s_have_seen_executable = True;
      // Twice, one for the process, one for the thread.
      HChar const* const* event_names = (HChar const* const[]){"process_create", "thread_create"};
      for (SizeT i = 0; i < 2; ++i) {
         if (s_first_event)
            s_first_event = False;
         else
            VG_(fprintf)(fp, ",\n");

         VG_(fprintf)(fp,
                      "{\"type\": \"%s\", \"pid\": %d, \"parent_pid\": %d, \"executable\": \"",
                      event_names[i], VG_(getpid)(), VG_(getpid)());

         // Dump the filename escaped for JSON.
         for (HChar const* c = filename; *c != '\0'; c++) {
            switch (*c) {
            case '"':
               VG_(fprintf)(fp, "\\\"");
               break;
            case '\\':
               VG_(fprintf)(fp, "\\\\");
               break;
            default:
               VG_(fprintf)(fp, "%c", *c);
               break;
            }
         }

         VG_(fprintf)(fp,
                      "\", \"tid\": %u, \"timestamp\": %u, \"lost_samples\": %d, \"stack\": []}",
                      VG_(get_running_tid)(), VG_(read_millisecond_timer)(), 0);
      }
   }

   if (!s_have_seen_executable)
      return;

   SizeT number_of_ranges_to_emit = 1 + (s_initial_main_exec_ranges != NULL ? VG_(sizeXA)(s_initial_main_exec_ranges) : 0);
   for (SizeT i = 0; i < number_of_ranges_to_emit; ++i) {
      if (i > 0) {
         struct Range* r = VG_(indexXA)(s_initial_main_exec_ranges, (Word)(i - 1));
         a = r->start;
         len = r->size;
      }

      if (s_first_event)
         s_first_event = False;
      else
         VG_(fprintf)(fp, ",\n");

      VG_(fprintf)(fp,
                   "{\"type\": \"mmap\", \"ptr\": %lu, \"size\": %lu, \"pid\": %d, \"tid\": %u, \"timestamp\": %u, \"lost_samples\": %d, \"stack\": [], \"name\": \"",
                   (UWord)a, (UWord)len, VG_(getpid)(), VG_(get_running_tid)(),
                   VG_(read_millisecond_timer)(), 0);

      if (filename == NULL) {
         VG_(fprintf)(fp, "\"}");
         return;
      }

      // Dump the filename escaped for JSON.
      for (HChar const* c = filename; *c != '\0'; c++) {
         switch (*c) {
         case '"':
            VG_(fprintf)(fp, "\\\"");
            break;
         case '\\':
            VG_(fprintf)(fp, "\\\\");
            break;
         default:
            VG_(fprintf)(fp, "%c", *c);
            break;
         }
      }

      // Is this rodata? text? relro? data? bss? let's pretend it's all data.
      VG_(fprintf)(fp, ": .data");

      VG_(fprintf)(fp, "\"}");
   }

   // Drop the ranges we've already emitted.
   if (s_initial_main_exec_ranges != NULL) {
      VG_(deleteXA)(s_initial_main_exec_ranges);
      s_initial_main_exec_ranges = NULL;
   }
}

static Bool sp_process_cmd_line_option(HChar const* arg)
{
   if (VG_STR_CLO(arg, "--profiler-output", clo_profilergrind_out_file)) {}
   else if (VG_INT_CLO(arg, "--profiler-sample-time-ms", s_millisecond_sample_resolution)) {}
   else return False;
   return True;
}

static void sp_print_usage(void)
{
   VG_(printf)(
      "    --profiler-output=<file>  Output file for the profilergrind tool.\n"
      "    --profiler-sample-time-ms=<ms>  Sample time resolution in milliseconds.\n"
   );
}

static void sp_print_debug_usage(void)
{
   VG_(printf)("(none)\n");
}

static void sp_pre_clo_init(void)
{
   VG_(details_name)            ("Serenity-Profilergrind");
   VG_(details_version)         (NULL);
   VG_(details_description)     ("the better callgrind tool");
   VG_(details_copyright_author)(
      "Copyright (C) 2023, by Ali Mohammadpur.");
   VG_(details_bug_reports_to)  (VG_BUGS_TO);

   VG_(details_avg_translation_sizeB) ( 275 );

   VG_(basic_tool_funcs)        (sp_post_clo_init,
                                 sp_instrument,
                                 sp_fini);

   VG_(track_new_mem_startup)(sp_track_new_mem_mmap);
   VG_(track_new_mem_mmap)   (sp_track_new_mem_mmap);

   VG_(needs_command_line_options)(sp_process_cmd_line_option,
                                   sp_print_usage,
                                   sp_print_debug_usage);
}

VG_DETERMINE_INTERFACE_VERSION(sp_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
