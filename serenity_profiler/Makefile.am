include $(top_srcdir)/Makefile.tool.am

EXTRA_DIST = docs/sp-manual.xml

#----------------------------------------------------------------------------
# serenity_profiler-<platform>
#----------------------------------------------------------------------------
AM_CPPFLAGS_@VGCONF_PLATFORM_PRI_CAPS@ += \
	-I$(top_srcdir)/coregrind

noinst_PROGRAMS  = serenity_profiler-@VGCONF_ARCH_PRI@-@VGCONF_OS@
if VGCONF_HAVE_PLATFORM_SEC
noinst_PROGRAMS += serenity_profiler-@VGCONF_ARCH_SEC@-@VGCONF_OS@
endif

serenity_profiler_SOURCES_COMMON = sp_main.c

serenity_profiler_@VGCONF_ARCH_PRI@_@VGCONF_OS@_SOURCES      = \
	$(serenity_profiler_SOURCES_COMMON)
serenity_profiler_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_PRI_CAPS@) \
	-I$(top_srcdir)/coregrind
serenity_profiler_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CFLAGS       = $(LTO_CFLAGS) \
	$(AM_CFLAGS_@VGCONF_PLATFORM_PRI_CAPS@) \
	-I$(top_srcdir)/coregrind
serenity_profiler_@VGCONF_ARCH_PRI@_@VGCONF_OS@_DEPENDENCIES = \
	$(TOOL_DEPENDENCIES_@VGCONF_PLATFORM_PRI_CAPS@)
serenity_profiler_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDADD        = \
	$(TOOL_LDADD_@VGCONF_PLATFORM_PRI_CAPS@)
serenity_profiler_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDFLAGS      = \
	$(TOOL_LDFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)
serenity_profiler_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LINK = \
	$(top_builddir)/coregrind/link_tool_exe_@VGCONF_OS@ \
	@VALT_LOAD_ADDRESS_PRI@ \
	$(LINK) \
	$(serenity_profiler_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CFLAGS) \
	$(serenity_profiler_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDFLAGS)

if VGCONF_HAVE_PLATFORM_SEC
serenity_profiler_@VGCONF_ARCH_SEC@_@VGCONF_OS@_SOURCES      = \
	$(serenity_profiler_SOURCES_COMMON)
serenity_profiler_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_SEC_CAPS@) \
	-I$(top_srcdir)/coregrind
serenity_profiler_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CFLAGS       = $(LTO_CFLAGS) \
	$(AM_CFLAGS_@VGCONF_PLATFORM_SEC_CAPS@) \
	-I$(top_srcdir)/coregrind
serenity_profiler_@VGCONF_ARCH_SEC@_@VGCONF_OS@_DEPENDENCIES = \
	$(TOOL_DEPENDENCIES_@VGCONF_PLATFORM_SEC_CAPS@)
serenity_profiler_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDADD        = \
	$(TOOL_LDADD_@VGCONF_PLATFORM_SEC_CAPS@)
serenity_profiler_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDFLAGS      = \
	$(TOOL_LDFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
serenity_profiler_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LINK = \
	$(top_builddir)/coregrind/link_tool_exe_@VGCONF_OS@ \
	@VALT_LOAD_ADDRESS_SEC@ \
	$(LINK) \
	$(serenity_profiler_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CFLAGS) \
	$(serenity_profiler_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDFLAGS)
endif
