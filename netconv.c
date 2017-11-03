/****************************************************************************/
/* netconv.c                                                                */

#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "netconv.h"

char *nc_rundir;

extern int mc_verbose;

/****************************************************************************/
/* nc_find (make sure a file exists and is executable)			    */
/* return 1 if error, 0 if ok						    */

char nc_find (char *s)
{
	struct stat statbuf;
	if (stat(s,&statbuf)
		|| (statbuf.st_mode & S_IFDIR)
		|| !(statbuf.st_mode & S_IEXEC)) return 1;
	return 0;
}

/****************************************************************************/
/* nc_try (auxiliary function for nc_search)				    */

char nc_try(char *dir, char *program, char *args)
{
	char *s = malloc(strlen(dir)+strlen(program)+strlen(args)+3);

	sprintf(s,"%s/%s",dir,program);
	if (nc_find(s)) return 1;

	sprintf(s,"%s/%s %s",dir,program,args);
	if (mc_verbose) printf("executing %s\n",s);
	system(s);

	free(s);
	return 0;
}


/****************************************************************************/
/* nc_run_spin								    */
/* Searches for the Spin executable and calls it (via system()). Spin is    */
/* looked for  in a number of paths starting at the directory given by the  */
/* SPINDIR environment variable, the path returned by nc_get_path, and then */
/* all the directories listed in $PATH. If Spin is found, it's called       */
/* with the given arguments.						    */

void nc_run_spin(char *args)
{
	char *s, *c, *env;

	s = getenv("SPINDIR");
	if (s && !nc_try(s,"spin",args)) return;
	if (!nc_try(nc_rundir,"spin",args)) return;

	env = s = strdup(getenv("PATH"));
	while (*s)
	{
		c = strchr(s,':');
		if (c) *c = 0;
		if (!nc_try(s,"spin",args)) { free(env); return; }
		if (c) s = c+1; else *s = 0;
	}
	free(env);
	fprintf(stderr,"error: did not find spin executable\n");
}

/****************************************************************************/

char *dirname (char *path)
{
	char *newpath, *slash;
	int length;

	if (!(slash = strrchr(path, '/')))
	{
		path = ".";
		length = 1;
	}
	else
	{
		while (slash > path && *slash == '/') --slash;
		length = slash - path + 1;
	}

	newpath = malloc(length+1);
	strncpy(newpath,path,length);
	newpath[length] = 0;
	return newpath;
}

/****************************************************************************/
/* Tries to determine the directory from which the checker was called.	    */

char* nc_get_path(char *argv0)
{
	char *dpath, *env, *s, *c;

	if (!nc_find(argv0)) return dirname(argv0);

	env = s = strdup(getenv("PATH"));
	while (*s)
	{
		c = strchr(s,':');
		if (c) *c = 0;

		dpath = malloc(strlen(s)+2+strlen(argv0));
		sprintf(dpath,"%s/%s",s,argv0);

		if (!nc_find(s))
		{
			free(dpath);
			return s;
		}

		free(dpath);
		if (c) s = c+1; else *s = 0;
	}

	/* couldn't locate myself - return cwd as default */
	free(env);
	return strdup(".");
}
