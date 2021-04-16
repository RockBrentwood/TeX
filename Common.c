// This file is part of CWEB.
// This program by Silvio Levy and Donald E. Knuth
// is based on a program by Knuth.
// It is distributed WITHOUT ANY WARRANTY, express or implied.
// Version 3.64 ↓- January 2002

// Copyright (C) 1987, 1990, 1993, 2000 Silvio Levy and Donald E. Knuth

// Permission is granted to make and distribute verbatim copies of this
// document provided that the copyright notice and this permission notice
// are preserved on all copies.

// Permission is granted to copy and distribute modified versions of this
// document under the conditions for verbatim copying, provided that the
// entire resulting derived work is given a different name and distributed
// under the terms of a permission notice identical to this one.

// ‹def›‹v›{‹char›'174}	%% vertical (|) in typewriter font

// ‹def›‹title›{Common code for CTANGLE and CWEAVE (Version 3.64)}
// ‹def›‹topofcontents›{
// ‹null›‹vfill›
//   ‹centerline›{
//      ‹title›font Common code for {‹ttitlefont› CTANGLE} and {‹ttitlefont› CWEAVE}
//   }
// ‹skip› 15pt
//  ‹centerline›{ (Version 3.64) }
// ‹fill›
//
// ‹def›‹botofcontents›{
// ‹vfill›‹noindent›
//   Copyright ‹copyright› 1987, 1990, 1993, 2000 Silvio Levy and Donald E. Knuth
// ‹bigskip›‹noindent›
//   Permission is granted to make and distribute verbatim copies of this
//   document provided that the copyright notice and this permission notice
//   are preserved on all copies.

// ‹smallskip›‹noindent›
//   Permission is granted to copy and distribute modified versions of this
//   document under the conditions for verbatim copying, provided that the
//   entire resulting derived work is given a different name and distributed
//   under the terms of a permission notice identical to this one.
//

// ‹pageno› = ‹contentspagenumber› ‹advance›‹pageno› by 1
// ‹let›‹maybe› = ‹iftrue›
// #format not_eq normal	// unreserve a C↑ keyword

// §1. Introduction.
// †1.0.1:
// This file contains code common to both ≪CTANGLE≫ and ≪CWEAVE≫, which roughly concerns the following problems:
// character uniformity, input routines, error handling and parsing of command line.
// We have tried to concentrate in this file all the system dependencies, so as to maximize portability.

// In the texts below we will sometimes use ≪CWEB≫ to refer to either of the two component programs, if no confusion can arise.

// The file begins with a few basic definitions.

// †1.1.1: Include files (1/3)
// ≪CWEB≫ uses the conventions of ‹C99› programs found in the standard ≪{ctype.h≫ header file.
#include <ctype.h>
// 1.1.1†2.2: Include files (2/3)
#include <stdio.h>
// 2.2†2.16: Include files (3/3)
// When an ≪@i≫ line is found in the ≪cur_file≫, we must temporarily stop reading it and start reading from the named include file.
// The ≪@i≫ line should give a complete file name with or without double quotes.
// If the environment variable ≪CWEBINPUTS≫ is set, or if the compiler flag of the same name was defined at compile time,
// ≪CWEB≫ will look for include files in the directory thus named, if it cannot find them in the current directory.
// (Colon-separated paths are not supported.)
// The remainder of the ≪@i≫ line after the file name is ignored.
#define too_long() { include_depth↓, err_print("! Include file name too long"); goto restart; }
#include <stdlib.h>	// declaration of ≪getenv≫ and ≪exit≫
// 2.16†

// #defines here

// †1.0.2: Definitions that should agree with ≪CTANGLE≫ and ≪CWEAVE≫ (1/10)
// In certain cases ≪CTANGLE≫ and ≪CWEAVE≫ should do almost, but not quite, the same thing.
// In these cases we've written common code for both, differentiating between the two by means of the global variable ≪program≫.
#define ctangle 0
#define cweave 1

typedef short boolean;
boolean program;	// ≪CWEAVE≫ or ≪CTANGLE≫?

// 1.0.2†2.1: Definitions that should agree with ≪CTANGLE≫ and ≪CWEAVE≫ (2/10)
// The lowest level of input to the ≪CWEB≫ programs is performed by ≪input_ln≫, which must be told which file to read from.
// The return value of ≪input_ln≫ is 1 if the read is successful and 0 if not (generally this means the file has ended).
// The conventions of ‹TeX› are followed; i.e., the characters of the next line of the file are copied into the ≪buffer≫ array,
// and the global variable ≪limit≫ is set to the first unoccupied position.
// Trailing blanks are ignored.
// The value of ≪limit≫ must be strictly less than ≪buf_size≫, so that ≪buffer[buf_size - 1]≫ is never filled.

// Since ≪buf_size≫ is strictly less than ≪long_buf_size≫,
// some of ≪CWEB≫'s routines use the fact that it is safe to refer to ≪*(limit + 2)≫ without overstepping the bounds of the array.
#define buf_size 100	// for ≪CWEAVE≫ and ≪CTANGLE≫
#define longest_name 10000
#define long_buf_size (buf_size + longest_name)	// for ≪CWEAVE≫
#define xisspace(c) (isspace(c) ∧ (unsigned char)(c) < 0x80)
#define xisupper(c) (isupper(c) ∧ (unsigned char)(c) < 0x80)

char buffer[long_buf_size];	// where each line of input goes
char *buffer_end = buffer + buf_size - 2;	// end of ≪buffer≫
char *limit = buffer;	// points to the last character in the buffer
char *loc = buffer;	// points to the next character to be read from the buffer

// 2.1†2.4: Definitions that should agree with ≪CTANGLE≫ and ≪CWEAVE≫ (3/10)
// Now comes the problem of deciding which file to read from next.
// Recall that the actual text that ≪CWEB≫ should process comes from two streams:
// a ≪web_file≫, which can contain possibly nested include commands ≪@i≫, and a ≪change_file≫, which might also contain includes.
// The ≪web_file≫ together with the currently open include files form a stack ≪file≫, whose names are stored in a parallel stack ≪file_name≫.
// The boolean ≪changing≫ tells whether or not we're reading from the ≪change_file≫.

// The line number of each open file is also kept for error reporting and for the benefit of ≪CTANGLE≫.

// #format line x	// make ≪line≫ an unreserved word
#define max_include_depth 10			// maximum number of source files open simultaneously, not counting the change file
#define max_file_name_length 60
#define cur_file file[include_depth]		// current file
#define cur_file_name file_name[include_depth]	// current file name
#define cur_line line[include_depth]		// number of current line in current file
#define web_file file[0]			// main source file
#define web_file_name file_name[0]		// main source file name

int include_depth;			// current level of nesting
FILE *file[max_include_depth];		// stack of non-change files
FILE *change_file;			// change file
char file_name[max_include_depth][max_file_name_length];	// stack of non-change file names
char change_file_name[max_file_name_length];	// name of change file
char alt_web_file_name[max_file_name_length];	// alternate name to try
int line[max_include_depth];		// number of current line in the stacked files
int change_line;			// number of current line in change file
int change_depth;			// where ≪@y≫ originated during a change
boolean input_has_ended;		// if there is no more input
boolean changing;			// if the current line is from ≪change_file≫
boolean web_file_open = 0;		// if the web file is being read

// 2.4†2.14: Definitions that should agree with ≪CTANGLE≫ and ≪CWEAVE≫ (4/10)
// The ≪get_line≫ procedure is called when ≪loc > limit≫; it puts the next line of merged input into the buffer and updates the other variables appropriately.
// A space is placed at the right end of the line.
// This procedure returns ≪!input_has_ended≫ because we often want to check the value of that variable after calling the procedure.

// If we've just changed from the ≪cur_file≫ to the ≪change_file≫,
// or if the ≪cur_file≫ has changed, we tell ≪CTANGLE≫ to print this information in the ‹C99› file by means of the ≪print_where≫ flag.
#define max_sections 2000	// number of identifiers, strings, section names; must be less than 0x2800

typedef unsigned short sixteen_bits;
sixteen_bits section_count;		// the current section number
boolean changed_section[max_sections];	// is the section changed?
boolean change_pending;			// if the current change is not yet recorded in ≪changed_section[section_count]≫
boolean print_where = 0;		// should ≪CTANGLE≫ print line and file info?

// 2.14†3.1: Definitions that should agree with ≪CTANGLE≫ and ≪CWEAVE≫ (5/10)
// Both ≪CWEAVE≫ and ≪CTANGLE≫ store identifiers, section names and other strings in a large array of ≪char≫s, called ≪byte_mem≫.
// Information about the names is kept in the array ≪name_dir≫, whose elements are structures of type ≪name_info≫,
// containing a pointer into the ≪byte_mem≫ array (the address where the name begins) and other data.
// A ≪name_pointer≫ variable is a pointer into ≪name_dir≫.
#define max_bytes 90000	// the number of bytes in identifiers, index entries, and section names; must be less than 2²⁴
#define max_names 4000	// number of identifiers, strings, section names; must be less than 0x2800

typedef struct name_info {
   char *byte_start;	// beginning of the name in ≪byte_mem≫
// †3.5: More elements of ≪name_info≫ structure (1/3)
// The names of identifiers are found by computing a hash address ≪h≫
// and then looking at strings of bytes signified by the ≪name_pointer≫s ≪hash[h]≫, ≪hash[h]→link≫, ≪hash[h]→link→link≫, \dots,
// until either finding the desired name or encountering the null pointer.
   struct name_info *link;
// 3.5†3.14: More elements of ≪name_info≫ structure (2/3)
// The names of sections are stored in ≪byte_mem≫ together with the identifier names,
// but a hash table is not used for them because ≪CTANGLE≫ needs to be able to recognize a section name when given a prefix of that name.
// A conventional binary search tree is used to retrieve section names, with fields called ≪llink≫ and ≪rlink≫ (where ≪llink≫ takes the place of ≪link≫).
// The root of this tree is stored in ≪name_dir→rlink≫; this will be the only information in ≪name_dir[0]≫.

// Since the space used by ≪rlink≫ has a different function for identifiers than for section names, we declare it as a ≪union≫.
#define llink link		// left link in binary search tree for section names
#define rlink dummy.Rlink	// right link in binary search tree for section names
#define root name_dir→rlink	// the root of the binary search tree for section names
   union {
      struct name_info *Rlink;	// right link in binary search tree for section names
      char Ilk;			// used by identifiers in ≪CWEAVE≫ only
   } dummy;
// 3.14†3.29: More elements of ≪name_info≫ structure (3/3)
// The last component of ≪name_info≫ is different for ≪CTANGLE≫ and ≪CWEAVE≫.
// In ≪CTANGLE≫, if ≪p≫ is a pointer to a section name, ≪p→equiv≫ is a pointer to its replacement text, an element of the array ≪text_info≫.
// In ≪CWEAVE≫, on the other hand, if ≪p≫ points to an identifier, ≪p→xref≫ is a pointer to its list of cross-references, an element of the array ≪xmem≫.
// The make-up of ≪text_info≫ and ≪xmem≫ is discussed in the ≪CTANGLE≫ and ≪CWEAVE≫ source files, respectively;
// here we just declare a common field ≪equiv_or_xref≫ as a pointer to a ≪char≫.
   char *equiv_or_xref;	// info corresponding to names
// 3.29†
} name_info;	// contains information about an identifier or section name
typedef name_info *name_pointer;			// pointer into array of ≪name_info≫s
char byte_mem[max_bytes];				// characters of names
char *byte_mem_end = byte_mem + max_bytes - 1;		// end of ≪byte_mem≫
name_info name_dir[max_names];				// information about names
name_pointer name_dir_end = name_dir + max_names - 1;	// end of ≪name_dir≫

// 3.1†3.3: Definitions that should agree with ≪CTANGLE≫ and ≪CWEAVE≫ (6/10)
// The first unused position in ≪byte_mem≫ and ≪name_dir≫ is kept in ≪byte_ptr≫ and ≪name_ptr≫, respectively.
// Thus we usually have ≪name_ptr→byte_start ≡ byte_ptr≫, and certainly we want to keep ≪name_ptr ≤ name_dir_end≫ and ≪byte_ptr ≤ byte_mem_end≫.
name_pointer name_ptr;	// first unused position in ≪name_dir≫
char *byte_ptr;		// first unused position in ≪byte_mem≫

// 3.3†3.6: Definitions that should agree with ≪CTANGLE≫ and ≪CWEAVE≫ (7/10)
// The hash table itself consists of ≪hash_size≫ entries of type ≪name_pointer≫, and is updated by the ≪id_lookup≫ procedure,
// which finds a given identifier and returns the appropriate ≪name_pointer≫.
// The matching is done by the function ≪names_match≫, which is slightly different in ≪CWEAVE≫ and ≪CTANGLE≫.
// If there is no match for the identifier, it is inserted into the table.
#define hash_size 353	// should be prime

typedef name_pointer *hash_pointer;
name_pointer hash[hash_size];			// heads of hash lists
hash_pointer hash_end = hash + hash_size - 1;	// end of ≪hash≫
hash_pointer h;					// index into hash-head array

// 3.6†4.1: Definitions that should agree with ≪CTANGLE≫ and ≪CWEAVE≫ (8/10)
// A global variable called ≪history≫ will contain one of four values at the end of every run:
//	≪spotless≫ means that no unusual messages were printed;
//	≪harmless_message≫ means that a message of possible interest was printed but no serious errors were detected;
//	≪error_message≫ means that at least one error was found;
//	≪fatal_message≫ means that the program terminated abnormally.
// The value of ≪history≫ does not influence the behavior of the program; it is simply computed for the convenience of systems that might want to use such information.
#define spotless		0	// ≪history≫ value for normal jobs
#define harmless_message	1	// ≪history≫ value when non-serious info was printed
#define error_message		2	// ≪history≫ value when an error was noted
#define fatal_message		3	// ≪history≫ value when we had to stop prematurely
inline void mark_harmless(void) { if (history ≡ spotless) history = harmless_message; }
#define mark_error() history = error_message

int history = spotless;	// indicates how bad this run was

// 4.1†5.1: Definitions that should agree with ≪CTANGLE≫ and ≪CWEAVE≫ (9/10)
// The user calls ≪CWEAVE≫ and ≪CTANGLE≫ with arguments on the command line.
// These are either file names or flags to be turned off (beginning with ≪"-"≫) or flags to be turned on (beginning with ≪"+"≫).
// The following globals are for communicating the user's desires to the rest of the program.
// The various file name variables contain strings with the names of those files. Most of the 0x80 flags are undefined but available for future extensions.
#define show_banner	flags['b']	// should the banner line be printed?
#define show_progress	flags['p']	// should progress reports be printed?
#define show_stats	flags['s']	// should statistics be printed at end of run?
#define show_happiness	flags['h']	// should lack of errors be announced?

int argc;	// copy of ≪ac≫ parameter to ≪main≫
char **argv;	// copy of ≪av≫ parameter to ≪main≫
char C_file_name[max_file_name_length];	// name of ≪C_file≫
char tex_file_name[max_file_name_length];	// name of ≪tex_file≫
char idx_file_name[max_file_name_length];	// name of ≪idx_file≫
char scn_file_name[max_file_name_length];	// name of ≪scn_file≫
boolean flags[0x80];	// an option for each 7-bit code

// 5.1†6.1: Definitions that should agree with ≪CTANGLE≫ and ≪CWEAVE≫ (10/10)
// Here is the code that opens the output file: ⁅00⁆
FILE *C_file;		// where output of ≪CTANGLE≫ goes
FILE *tex_file;		// where output of ≪CWEAVE≫ goes
FILE *idx_file;		// where index from ≪CWEAVE≫ goes
FILE *scn_file;		// where list of sections from ≪CWEAVE≫ goes
FILE *active_file;	// currently active file for ≪CWEAVE≫ output
// 6.1†

// †1.0.3: Other definitions (1/2)
// ≪CWEAVE≫ operates in three phases: First it inputs the source file and stores cross-reference data,
// then it inputs the source once again and produces the ‹TeX› output file, and finally it sorts and outputs the index.
// Similarly, ≪CTANGLE≫ operates in two phases.
// The global variable ≪phase≫ tells which phase we are in.
int phase;	// which phase are we in?
// 1.0.3†2.5: Other definitions (2/2)
// When ≪changing ≡ 0≫, the next line of ≪change_file≫ is kept in ≪change_buffer≫, for purposes of comparison with the next line of ≪cur_file≫.
// After the change file has been completely input, we set ≪change_limit = change_buffer≫, so that no further matches will be made.

// Here's a shorthand expression for inequality between the two lines:
#define lines_dont_match (change_limit - change_buffer ≠ limit - buffer ∨ strncmp(buffer, change_buffer, limit - buffer) ≠ 0)

char change_buffer[buf_size];	// next line of ≪change_file≫
char *change_limit;		// points to the last character in ≪change_buffer≫
// 2.5†

// †3.7: Predeclaration of procedures (1/8)
extern int names_match(name_pointer p, char *first, int l, eight_bits t);

// 3.7†3.12: Predeclaration of procedures (2/8)
// The information associated with a new identifier must be initialized in a slightly different way in ≪CWEAVE≫ than in ≪CTANGLE≫; hence the ≪init_p≫ procedure.
void init_p(name_pointer p, eight_bits t);

// 3.12†3.20: Predeclaration of procedures (3/8)
// Adding a section name to the tree is straightforward if we know its parent and whether it's the ≪rlink≫ or ≪llink≫ of the parent.
// As a special case, when the name is the first section being added, we set the ‟parent” to ≪NULL≫.
// When a section name is created, it has only one chunk, which however may be just a prefix; the full name will hopefully be unveiled later.
// Obviously, ≪prefix_length≫ starts out as the length of the first chunk, though it may decrease later.

// The information associated with a new node must be initialized differently in ≪CWEAVE≫ and ≪CTANGLE≫;
// hence the ≪init_node≫ procedure, which is defined differently in ≪cweave.w≫ and ≪ctangle.w≫.
extern void init_node(name_pointer node);

// 3.20†3.27: Predeclaration of procedures (4/8)
// The return codes of ≪section_name_cmp≫, which compares a string with the full name of a section,
// are those of ≪web_strcmp≫ plus ≪bad_extension≫, used when the string is an extension of a supposedly already complete section name.
// This function has a side effect when the comparison string is an extension:
// It advances the address of the first character of the string by an amount equal to the length of the known part of the section name.

// The name ≪@<foo...@>≫ should be an acceptable ‟abbreviation” for ≪@<foo@>≫.
// If such an abbreviation comes after the complete name, there's no trouble recognizing it.
// If it comes before the complete name, we simply append a null chunk.
// This logic requires us to regard ≪@<foo...@>≫ as an ‟extension” of itself.
#define bad_extension 5

int section_name_cmp(char **pfirst, int len, name_pointer r);

// 3.27†4.2: Predeclaration of procedures (5/8)
// The command ‛≪err_print("! Error message")≫’ will report a syntax error to the user,
// by printing the error message at the beginning of a new line and then giving an indication of where the error was spotted in the source file.
// Note that no period follows the error message, since the error routine will automatically supply a period.
// A newline is automatically supplied if the string begins with ≪"!"≫.
void err_print(char *s);

// 4.2†4.5: Predeclaration of procedures (6/8)
// When no recovery from some error has been provided, we have to wrap up and quit as graciously as possible.
// This is done by calling the function ≪wrap_up≫ at the end of the code.

// ≪CTANGLE≫ and ≪CWEAVE≫ have their own notions about how to print the job statistics.
int wrap_up(void);
extern void print_stats(void);

// 4.5†4.8: Predeclaration of procedures (7/8)
// When there is no way to recover from an error, the ≪fatal≫ subroutine is invoked.
// This happens most often when ≪overflow≫ occurs.
void fatal(char *s, char *t);
void overflow(char *t);

// 4.8†5.3: Predeclaration of procedures (8/8)
// We now must look at the command line arguments and set the file names accordingly.
// At least one file name must be present: the ≪CWEB≫ file.
// It may have an extension, or it may omit the extension to get ≪".w"≫ or ≪".web"≫ added.
// The ‹TeX› output file name is formed by replacing the ≪CWEB≫ file name extension by ≪".tex"≫,
// and the ‹C99› file name by replacing the extension by ≪".c"≫, after removing the directory name (if any).

// If there is a second file name present among the arguments, it is the change file, again either with an extension or without one to get ≪".ch"≫.
// An omitted change file argument means that ≪"/dev/null"≫ should be used, when no changes are desired. ⁅01⁆

// If there's a third file name, it will be the output file.
void scan_args(void);
// 5.3†

// 1.0.1†1.0.4:
// There's an initialization procedure that gets both ≪CTANGLE≫ and ≪CWEAVE≫ off to a good start.
// We will fill in the details of this procedure later.
void common_init(void) {
// †3.4: Initialize pointers (1/3)
   name_dir→byte_start = byte_ptr = byte_mem;	// position zero in both arrays
   name_ptr = name_dir + 1;			// ≪name_dir[0]≫ will be used only for error recovery
   name_ptr→byte_start = byte_mem;		// this makes name 0 of length zero
// 3.4†3.8: Initialize pointers (2/3)
// Initially all the hash lists are empty.
   for (h = hash; h ≤ hash_end; *h↑ = NULL) ;
// 3.8†3.15: Initialize pointers (3/3)
   root = NULL;	// the binary search tree starts out with nothing in it
// 3.15†5.2: Set the default options common to ≪CTANGLE≫ and ≪CWEAVE≫
// The ≪flags≫ will be initially zero.
// Some of them are set to 1 before scanning the arguments; if additional flags are 1 by default they should be set before calling ≪common_init≫.
   show_banner = show_happiness = show_progress = 1;
// 5.2†6.2: Scan arguments and open output files
   scan_args();
   if (program ≡ ctangle) {
      C_file = fopen(C_file_name, "w"); if (C_file ≡ NULL) fatal("! Cannot open output file ", C_file_name);	// ⁅02⁆
   } else {
      tex_file = fopen(tex_file_name, "w"); if (tex_file ≡ NULL) fatal("! Cannot open output file ", tex_file_name);
   }
// 6.2†
}
// 1.0.4†

// ‡1.1. The Character Set.
// †1.1.2:
// A few character pairs are encoded internally as single characters, using the definitions below.
// These definitions are consistent with an extension of ASCII code originally developed at MIT and explained in Appendix C of ≪_ The ‹TeX›book _≫;
// thus, users who have such a character set can type things like ≪‹char›'32≫ and ≪‹char›'4≫ instead of ≪!=≫ and ≪&&≫.
// (However, their files will not be too portable until more people adopt the extended code.)

// If the character set is not ASCII, the definitions given here may conflict with existing characters; in such cases, other arbitrary codes should be substituted.
// The indexes to ≪CTANGLE≫ and ≪CWEAVE≫ mention every case where similar codes may have to be changed in order to avoid character conflicts.
// Look for the entry ‟ASCII code dependencies” in those indexes. ⁅03⁆⁅04⁆
#define and_and		0x04	// ‛≪&&≫’; corresponds to MIT's {‹tentex›‹char›'4}
#define lt_lt		0x10	// ‛≪<<≫’; corresponds to MIT's {‹tentex›‹char›'20}
#define gt_gt		0x11	// ‛≪>>≫’; corresponds to MIT's {‹tentex›‹char›'21}
#define plus_plus	0x0b	// ‛≪++≫’; corresponds to MIT's {‹tentex›‹char›'13}
#define minus_minus	0x01	// ‛≪--≫’; corresponds to MIT's {‹tentex›‹char›'1}
#define minus_gt	0x19	// ‛≪->≫’; corresponds to MIT's {‹tentex›‹char›'31}
#define not_eq		0x1a	// ‛≪!=≫’; corresponds to MIT's {‹tentex›‹char›'32}
#define lt_eq		0x1c	// ‛≪<=≫’; corresponds to MIT's {‹tentex›‹char›'34}
#define gt_eq		0x1d	// ‛≪>=≫’; corresponds to MIT's {‹tentex›‹char›'35}
#define eq_eq		0x1e	// ‛≪==≫’; corresponds to MIT's {‹tentex›‹char›'36}
#define or_or		0x1f	// ‛≪||≫’; corresponds to MIT's {‹tentex›‹char›'37}
#define dot_dot_dot	0x0e	// ‛≪...≫’; corresponds to MIT's {‹tentex›‹char›'16}
#define colon_colon	0x06	// ‛≪::≫’; corresponds to MIT's {‹tentex›‹char›'6}
#define period_ast	0x16	// ‛≪.*≫’; corresponds to MIT's {‹tentex›‹char›'26}
#define minus_gt_ast	0x17	// ‛≪→*≫’; corresponds to MIT's {‹tentex›‹char›'27}
// 1.1.2†

// §2. Input Routines.
// †2.3:
// In the unlikely event that your standard I/O library does not support ≪feof≫, ≪getc≫, and ≪ungetc≫ you may have to change things here. ⁅05⁆

// fp: what file to read from
int input_ln(FILE *fp) {	// copies a line into ≪buffer≫ or returns 0
   register int c = EOF;	// character read; initialized so some compilers won't complain
   if (feof(fp)) return 0;	// we have hit end-of-file
   register char *k = limit = buffer;	// where next character goes: starting at the beginning of buffer
   while (k ≤ buffer_end ∧ (c = getc(fp)) ≠ EOF ∧ c ≠ '\n') if ((*k↑ = c) ≠ ' ') limit = k;
   if (k > buffer_end) {
      c = getc(fp); if (c ≠ EOF ∧ c ≠ '\n') ungetc(c, fp), loc = buffer, err_print("! Input line too long");	// ⁅06⁆
   }
   return c ≠ EOF ∨ limit ≠ buffer;	// false means there was nothing after the last newline
}

// 2.3†2.6:
// Procedure ≪prime_the_change_buffer≫ sets ≪change_buffer≫ in preparation for the next matching operation.
// Since blank lines in the change file are not used for matching, we have ≪(change_limit ≡ change_buffer ∧ !changing)≫ if and only if the change file is exhausted.
// This procedure is called only when ≪changing≫ is 1; hence error messages will be reported correctly.
void prime_the_change_buffer(void) {
   change_limit = change_buffer;	// this value is used if the change file ends
// †2.7: Skip over comment lines in the change file; ≪return≫ if end of file
// While looking for a line that begins with ≪@x≫ in the change file, we allow lines that begin with ≪@≫, as long as they don't begin with ≪@y≫, ≪@z≫, or ≪@i≫
// (which would probably mean that the change file is fouled up).
   while (1) {
      change_line↑;
      if (!input_ln(change_file)) return;
      else if (limit < buffer + 2 ∨ buffer[0] ≠ '@') continue;
      else if (xisupper(buffer[1])) buffer[1] = tolower(buffer[1]);
      if (buffer[1] ≡ 'x') break;
      else if (buffer[1] ≡ 'y' ∨ buffer[1] ≡ 'z' ∨ buffer[1] ≡ 'i') loc = buffer + 2, err_print("! Missing @x in change file");	// ⁅07⁆
   }
// 2.7†2.8: Skip to the next nonblank line; ≪return≫ if end of file
// Here we are looking at lines following the ≪@x≫.
   do {
      change_line↑;
      if (!input_ln(change_file)) {
         err_print("! Change file ended after @x");	// ⁅08⁆
         return;
      }
   } while (limit ≡ buffer);
// 2.8†
   SwapBuffers();	// Move ≪buffer≫ and ≪limit≫ to ≪change_buffer≫ and ≪change_limit≫
}

// 2.6†2.9 [2]: Move ≪buffer≫ and ≪limit≫ to ≪change_buffer≫ and ≪change_limit≫
// Editor's Note:
// ∙	This was orginally a multiply-used module.
inline void SwapBuffers(void) {
   change_limit = change_buffer + (limit - buffer), strncpy(change_buffer, buffer, limit - buffer + 1);
}

// 2.9†2.10:
// The following procedure is used to see if the next change entry should go into effect; it is called only when ≪changing≫ is 0.
// The idea is to test whether or not the current contents of ≪buffer≫ matches the current contents of ≪change_buffer≫.
// If not, there's nothing more to do; but if so, a change is called for:
// All of the text down to the ≪@y≫ is supposed to match.
// An error message is issued if any discrepancy is found.
// Then the procedure prepares to read the next line from ≪change_file≫.

// When a match is found, the current section is marked as changed unless the first line after the ≪@x≫
// and after the ≪@y≫ both start with either ≪'@*'≫ or ≪'@ '≫ (possibly preceded by whitespace).

// This procedure is called only when ≪buffer < limit≫, i.e., when the current line is nonempty.
#define if_section_start_make_pending(b) { \
   *limit = '!'; \
   for (loc = buffer; xisspace(*loc); loc↑) ; \
   *limit = ' '; \
   if (*loc ≡ '@' ∧ (xisspace(*(loc + 1)) ∨ *(loc + 1) ≡ '*')) change_pending = b; \
}

void check_change(void) {	// switches to ≪change_file≫ if the buffers match
   int n = 0;	// the number of discrepancies found
   if (lines_dont_match) return;
   change_pending = 0;
   if (!changed_section[section_count]) {
      if_section_start_make_pending(1);
      if (!change_pending) changed_section[section_count] = 1;
   }
   while (1) {
      changing = 1, print_where = 1, change_line↑;
      if (!input_ln(change_file)) {
         err_print("! Change file ended before @y");	// ⁅09⁆
         change_limit = change_buffer, changing = 0;
         return;
      }
      if (limit > buffer + 1 ∧ buffer[0] ≡ '@') {
         char xyz_code = xisupper(buffer[1])? tolower(buffer[1]): buffer[1];
      // †2.11: If the current line starts with ≪@y≫, report any discrepancies and ≪return≫
         if (xyz_code ≡ 'x' ∨ xyz_code ≡ 'z') loc = buffer + 2, err_print("! Where is the matching @y?");	// ⁅10⁆
         else if (xyz_code ≡ 'y') {
            if (n > 0) loc = buffer + 2, printf("\n! Hmm... %d ", n), err_print("of the preceding lines failed to match");	// ⁅11⁆
            change_depth = include_depth;
            return;
         }
      // 2.11†
      }
      SwapBuffers();	// Move ≪buffer≫ and ≪limit≫ to ≪change_buffer≫ and ≪change_limit≫
      changing = 0, cur_line↑;
      while (!input_ln(cur_file)) {	// pop the stack or quit
         if (include_depth ≡ 0) {
            err_print("! CWEB file ended during a change");	// ⁅12⁆
            input_has_ended = 1; return;
         }
         include_depth↓, cur_line↑;
      }
      if (lines_dont_match) n↑;
   }
}

// 2.10†2.12:
// The ≪reset_input≫ procedure, which gets ≪CWEB≫ ready to read the user's ≪CWEB≫ input, is used at the beginning of phase one of ≪CTANGLE≫, phases one and two of ≪CWEAVE≫.
void reset_input(void) {
   limit = buffer, loc = buffer + 1, buffer[0] = ' ';
// †2.13: Open input files
// The following code opens the input files. ⁅13⁆
   web_file = fopen(web_file_name, "r");
   if (web_file ≡ NULL) {
      strcpy(web_file_name, alt_web_file_name);
      web_file = fopen(web_file_name, "r"); if (web_file ≡ NULL) fatal("! Cannot open input file ", web_file_name);
   }	// ⁅14⁆⁅15⁆
   web_file_open = 1;
   change_file = fopen(change_file_name, "r"); if (change_file ≡ NULL) fatal("! Cannot open change file ", change_file_name);
// 2.13†
   include_depth = 0, cur_line = 0, change_line = 0;
   change_depth = include_depth;
   changing = 1, prime_the_change_buffer(), changing = !changing;
   limit = buffer, loc = buffer + 1, buffer[0] = ' ', input_has_ended = 0;
}

// 2.12†2.15:
int get_line(void) {	// inputs the next line
restart:
   if (changing ∧ include_depth ≡ change_depth) {
   // †2.19: Read from ≪change_file≫ and maybe turn off ≪changing≫
      change_line↑;
      if (!input_ln(change_file)) err_print("! Change file ended without @z"), buffer[0] = '@', buffer[1] = 'z', limit = buffer + 2;	// ⁅16⁆
      if (limit > buffer) {	// check if the change has ended
         if (change_pending) {
            if_section_start_make_pending(0);
            if (change_pending) changed_section[section_count] = 1, change_pending = 0;
         }
         *limit = ' ';
         if (buffer[0] ≡ '@') {
            if (xisupper(buffer[1])) buffer[1] = tolower(buffer[1]);
            if (buffer[1] ≡ 'x' ∨ buffer[1] ≡ 'y') loc = buffer + 2, err_print("! Where is the matching @z?");	// ⁅17⁆
            else if (buffer[1] ≡ 'z') prime_the_change_buffer(), changing = !changing, print_where = 1;
         }
      }
   // 2.19†
   }
   if (!changing ∨ include_depth > change_depth) {
   // †2.18: Read from ≪cur_file≫ and maybe turn on ≪changing≫
      cur_line↑;
      for (; !input_ln(cur_file); cur_line↑) {	// pop the stack or quit
         print_where = 1;
         if (include_depth ≡ 0) { input_has_ended = 1; break; }
         fclose(cur_file), include_depth↓;
         if (changing ∧ include_depth ≡ change_depth) break;
      }
      if (!changing ∧ !input_has_ended ∧ limit - buffer ≡ change_limit - change_buffer ∧ buffer[0] ≡ change_buffer[0] ∧ change_limit > change_buffer) check_change();
   // 2.18†
      if (changing ∧ include_depth ≡ change_depth) goto restart;
   }
   if (input_has_ended) return 0;
   loc = buffer, *limit = ' ';
   if (buffer[0] ≡ '@' ∧ (buffer[1] ≡ 'i' ∨ buffer[1] ≡ 'I')) {
      loc = buffer + 2, *limit = '"';
      for (; *loc ≡ ' ' ∨ *loc ≡ '\t'; loc↑);
      if (loc ≥ limit) {
         err_print("! Include file name not given");	// ⁅18⁆
         goto restart;
      } else if (include_depth ≥ max_include_depth - 1) {
         err_print("! Too many nested includes");	// ⁅19⁆
         goto restart;
      } else include_depth↑;	// push input stack
   // †2.17: Try to open include file, abort push if unsuccessful, go to ≪restart≫
      char temp_file_name[max_file_name_length];
      char *cur_file_name_end = cur_file_name + max_file_name_length - 1;
      char *k = cur_file_name;
      if (*loc ≡ '"') {
         loc↑;
         for (; *loc ≠ '"' ∧ k ≤ cur_file_name_end; *k↑ = *loc↑);
         if (loc ≡ limit) k = cur_file_name_end + 1;	// unmatched quote is ‛too long’
      } else for (; *loc ≠ ' ' ∧ *loc ≠ '\t' ∧ *loc ≠ '"' ∧ k ≤ cur_file_name_end; *k↑ = *loc↑);
      if (k > cur_file_name_end) too_long();	// ⁅20⁆
      *k = '\0';
      cur_file = fopen(cur_file_name, "r");
      if (cur_file ≠ NULL) {
         cur_line = 0, print_where = 1;
         goto restart;	// success
      }
      char *kk = getenv("CWEBINPUTS");
      int l;	// length of file name
      if (kk ≠ NULL) {
         l = strlen(kk); if (l > max_file_name_length - 2) too_long();
         strcpy(temp_file_name, kk);
      } else {
#ifdef CWEBINPUTS
         l = strlen(CWEBINPUTS);
         if (l > max_file_name_length - 2) too_long();
         strcpy(temp_file_name, CWEBINPUTS);
#else
         l = 0;
#endif
      }
      if (l > 0) {
         if (k + l + 2 ≥ cur_file_name_end) too_long();	// ⁅21⁆
         for (; k ≥ cur_file_name; k↓) *(k + l + 1) = *k;
         strcpy(cur_file_name, temp_file_name);
         cur_file_name[l] = '/';	// ‹UNIX› pathname separator
         cur_file = fopen(cur_file_name, "r");
         if (cur_file ≠ NULL) {
            cur_line = 0, print_where = 1; goto restart;	// success
         }
      }
      include_depth↓, err_print("! Cannot open include file"); goto restart;
   // 2.17†
   }
   return 1;
}

// 2.15†2.20:
// At the end of the program, we will tell the user if the change file had a line that didn't match any relevant line in ≪web_file≫.
void check_complete(void) {
   if (change_limit ≠ change_buffer) {	// ≪changing≫ is 0
      strncpy(buffer, change_buffer, change_limit - change_buffer + 1);
      limit = buffer + (int)(change_limit - change_buffer);
      changing = 1, change_depth = include_depth, loc = buffer, err_print("! Change file entry did not match");	// ⁅22⁆
   }
}
// 2.20†

// §3. Storage of Names and Strings.
// †3.2:
// The actual sequence of characters in the name pointed to by a ≪name_pointer p≫ appears in positions ≪p→byte_start≫ to ≪(p + 1)→byte_start - 1≫, inclusive.
// The ≪print_id≫ macro prints this text on the user's terminal.

#define length(c) (c + 1)→byte_start - (c)→byte_start	// the length of a name
#define print_id(c) term_write((c)→byte_start, length((c)))	// print identifier

// 3.2†3.9;
// Here is the main procedure for finding identifiers:
// first: first character of string; last: last character of string plus one; t: the ≪ilk≫; used by ≪CWEAVE≫ only.
name_pointer id_lookup(char *first, char *last, char t) {	// looks up a string in the identifier table
   char *i = first;	// position in ≪buffer≫
   if (last ≡ NULL) for (last = first; *last ≠ '\0'; last↑);
   int l = last - first;	// compute the length of the given identifier
// †3.10: Compute the hash code ≪h≫
// A simple hash code is used: If the sequence of character codes is c_1 c_2 \ldots c_n$, its hash value will be $$(2ⁿ⁻¹ c_1 + 2ⁿ⁻² c_2 + ⋯ + c_n) \bmod ≪hash_size≫.$$
   int h = (unsigned char)*i;	// hash code
   for (; ↑i < last; h = (h + h + (int)(unsigned char)*i)%hash_size);	// ⁅23⁆
// 3.10†3.11: Compute the name location ≪p≫
// If the identifier is new, it will be placed in position ≪p = name_ptr≫, otherwise ≪p≫ will point to its existing location.
   name_pointer p = hash[h];	// where the identifier is being sought
   for (; p ≠ NULL ∧ !names_match(p, first, l, t); p = p→link);
   if (p ≡ NULL)
      p = name_ptr,	// the current identifier is new
      p→link = hash[h], hash[h] = p;	// insert ≪p≫ at beginning of hash list
// 3.11†
   if (p ≡ name_ptr) {
   // †3.13: Enter a new name into the table at position ≪p≫
      if (byte_ptr + l > byte_mem_end) overflow("byte memory");
      if (name_ptr ≥ name_dir_end) overflow("name");
      strncpy(byte_ptr, first, l);
      (↑name_ptr)→byte_start = byte_ptr += l;
      if (program ≡ cweave) init_p(p, t);
   // 3.13†
   }
   return p;
}

// 3.9†3.16: If ≪p≫ is a ≪name_pointer≫ variable, as we have seen, ≪p→byte_start≫ is the beginning of the area where the name corresponding to ≪p≫ is stored.
// However, if ≪p≫ refers to a section name, the name may need to be stored in chunks,
// because it may ‟grow”: a prefix of the section name may be encountered before the full name.
// Furthermore we need to know the length of the shortest prefix of the name that was ever encountered.

// We solve this problem by inserting two extra bytes at ≪p→byte_start≫, representing the length of the shortest prefix, when ≪p≫ is a section name.
// Furthermore, the last byte of the name will be a blank space if ≪p≫ is a prefix.
// In the latter case, the name pointer ≪p + 1≫ will allow us to access additional chunks of the name:
// The second chunk will begin at the name pointer ≪(p + 1)→link≫,
// and if it too is a prefix (ending with blank) its ≪link≫ will point to additional chunks in the same way.
// Null links are represented by ≪name_dir≫.
#define first_chunk(p)		((p)→byte_start + 2)
#define prefix_length(p)	(int)((unsigned char)*((p)→byte_start)*0x100 + (unsigned char)*((p)→byte_start + 1))
#define set_prefix_length(p, m)	(*((p)→byte_start) = (m)/0x100, *((p)→byte_start + 1) = (m)%0x100)

void print_section_name(name_pointer p) {
   char *s = first_chunk(p);
   name_pointer q = p + 1;
   while (p ≠ name_dir) {
      char *ss = (p + 1)→byte_start - 1;
      if (*ss ≡ ' ' ∧ ss ≥ s) term_write(s, ss-s), q = p = q→link;
      else term_write(s, ss + 1 - s), p = name_dir, q = NULL;
      s = p→byte_start;
   }
   if (q ≠ NULL) term_write("...", 3);	// complete name not yet known
}

// 3.16†3.17:
void sprint_section_name(char *dest, name_pointer p) {
   char *s = first_chunk(p);
   name_pointer q = p + 1;
   while (p ≠ name_dir) {
      char *ss = (p + 1)→byte_start - 1;
      if (*ss ≡ ' ' ∧ ss ≥ s) q = p = q→link;
      else ss↑, p = name_dir;
      strncpy(dest, s, ss - s), dest += ss - s, s = p→byte_start;
   }
   *dest = '\0';
}

// 3.17†3.18:
void print_prefix_name(name_pointer p) {
   char *s = first_chunk(p);
   int l = prefix_length(p);
   term_write(s, l);
   if (s + l < (p + 1)→byte_start) term_write("...", 3);
}

// 3.18†3.19:
// When we compare two section names, we'll need a function analogous to ≪strcmp≫.
// But we do not assume the strings are null-terminated, and we keep an eye open for prefixes and extensions.
#define less		0	// the first name is lexicographically less than the second
#define equal		1	// the first name is equal to the second
#define greater		2	// the first name is lexicographically greater than the second
#define prefix		3	// the first name is a proper prefix of the second
#define extension	4	// the first name is a proper extension of the second

// j, k: beginning of first and second strings; j_len, k_len: length of strings
int web_strcmp(char *j, int j_len, char *k, int k_len) {	// fuller comparison than ≪strcmp≫
  char *j1 = j + j_len, *k1 = k + k_len;
  for (; k < k1 ∧ j < j1 ∧ *j ≡ *k; k↑, j↑);
  return
     k ≡ k1? (j ≡ j1? equal: extension):
     j ≡ j1? prefix: *j < *k? less: greater;
}

// 3.19†3.21:
// par: parent of new node; c: right or left?;
// first: first character of section name; last: last character of section name, plus one;
// ispref: are we adding a prefix or a full name?
name_pointer add_section_name(name_pointer par, int c, char *first, char *last, int ispref) {	// install a new node in the tree
   name_pointer p = name_ptr;	// new node
   char *s = first_chunk(p);
   int name_len = last - first + ispref;	// length of section name
   if (s + name_len > byte_mem_end) overflow("byte memory");
   if (name_ptr + 1 ≥ name_dir_end) overflow("name");
   (↑name_ptr)→byte_start = byte_ptr = s + name_len;
   if (ispref) *(byte_ptr - 1) = ' ', name_len↓, name_ptr→link = name_dir, (↑name_ptr)→byte_start = byte_ptr;
   set_prefix_length(p, name_len), strncpy(s, first, name_len), p→rlink = p→llink = NULL;
   init_node(p);
   return par ≡ NULL? (root = p): c ≡ less? (par→llink = p): (par→rlink = p);
}

// 3.21†3.22:
// p: name to be extended; first: beginning of extension text; last: one beyond end of extension text; ispref: are we adding a prefix or a full name?
void extend_section_name(name_pointer p, char *first, char *last, int ispref) {
   name_pointer q = p + 1;
   int name_len = last - first + ispref;
   if (name_ptr ≥ name_dir_end) overflow("name");
   for (; q→link ≠ name_dir; q = q→link);
   q→link = name_ptr;
   char *s = name_ptr→byte_start;
   name_ptr→link = name_dir;
   if (s + name_len > byte_mem_end) overflow("byte memory");
   (↑name_ptr)→byte_start = byte_ptr = s + name_len;
   strncpy(s, first, name_len);
   if (ispref) *(byte_ptr - 1) = ' ';
}

// 3.22†3.23:
// The ≪section_lookup≫ procedure is supposed to find a section name that matches a new name, installing the new name if it doesn't match an existing one.
// The new name is the string between ≪first≫ and ≪last≫; a ‟match” means that the new name exactly equals or is a prefix or extension of a name in the tree.

// first, last: first and last characters of new name; int ispref: is the new name a prefix or a full name?
name_pointer section_lookup(char *first, char *last, int ispref) {	// is the new name a prefix or a full name?
   int c = 0;	// comparison between two names; initialized so some compilers won't complain
   name_pointer p = root;	// current node of the search tree
   name_pointer q = NULL;	// another place to look in the tree
   name_pointer r = NULL;	// where a match has been found
   name_pointer par = NULL;	// parent of ≪p≫, if ≪r≫ is ≪NULL≫; otherwise parent of ≪r≫
   int name_len = last - first + 1;
// †3.24: Look for matches for new name among shortest prefixes, complaining if more than one is found
// A legal new name matches an existing section name if and only if it matches the shortest prefix of that section name.iiiiiii
// Therefore we can limit our search for matches to shortest prefixes, which eliminates the need for chunk-chasing at this stage.
   while (p ≠ NULL) {	// compare shortest prefix of ≪p≫ with new name
      c = web_strcmp(first, name_len, first_chunk(p), prefix_length(p));
      if (c ≡ less ∨ c ≡ greater) {	// new name does not match ≪p≫
         if (r ≡ NULL) par = p;	// no previous matches have been found
         p = c ≡ less? p→llink: p→rlink;
      } else {	// new name matches ≪p≫
         if (r ≠ NULL) {	// and also ≪r≫: illegal
            printf("\n! Ambiguous prefix: matches <"),	// ⁅24⁆
            print_prefix_name(p), printf(">\n and <"), print_prefix_name(r), err_print(">");
            return name_dir;	// the unsection
         }
         r = p,	// remember match
         p = p→llink,	// try another
         q = r→rlink;	// we'll get back here if the new ≪p≫ doesn't match
      }
      if (p ≡ NULL) p = q, q = NULL;	// ≪q≫ held the other branch of ≪r≫
   }
// 3.24†3.25: If no match found, add new name to tree
   if (r ≡ NULL) return add_section_name(par, c, first, last + 1, ispref);	// no matches were found
// 3.25†3.26: If one match found, check for compatibility and return match
// Although error messages are given in anomalous cases, we do return the unique best match when a discrepancy is found,
// because users often change a title in one place while forgetting to change it elsewhere.
   switch (section_name_cmp(&first, name_len, r)) {	// compare all of ≪r≫ with new name
      case prefix:
         if (!ispref) printf("\n! New name is a prefix of <"), print_section_name(r), err_print(">");	// ⁅25⁆
         else if (name_len < prefix_length(r)) set_prefix_length(r, name_len);
      case equal:
      return r;
      case extension:
         if (!ispref ∨ first ≤ last) extend_section_name(r, first, last + 1, ispref);
      return r;
      case bad_extension: printf("\n! New name extends <"), print_section_name(r), err_print(">"); return r;	// ⁅26⁆
      default:	// no match: illegal
         printf("\n! Section name incompatible with <"),	// ⁅27⁆
         print_prefix_name(r), printf(">,\n which abbreviates <"), print_section_name(r), err_print(">");
      return r;
   }
// 3.26†
}

// 3.23†3.28:
// pfirst: pointer to beginning of comparison string; len: length of string; r: section name being compared.
int section_name_cmp(char **pfirst, int len, name_pointer r) {
   char *first = *pfirst;	// beginning of comparison string
   name_pointer q = r + 1;	// access to subsequent chunks
   char *s = first_chunk(r);
   while (1) {
      char *ss = (r + 1)→byte_start - 1;
      int ispref = *ss ≡ ' ' ∧ ss ≥ r→byte_start;	// is chunk ≪r≫ a prefix?
      if (ispref) q = q→link; else ss↑, q = name_dir;
      int c = web_strcmp(first, len, s, ss - s);	// comparison
      switch (c) {
         case equal:
            if (q ≠ name_dir) return q→byte_start ≡ (q + 1)→byte_start? equal: prefix;
            else if (!ispref) return equal;
            else {
               *pfirst = first + (ss - s); return extension;	// null extension
            }
         case extension:
            if (!ispref) return bad_extension;
            first += ss - s;
            if (q ≠ name_dir) { len -= ss - s, s = q→byte_start, r = q; continue; }
            *pfirst = first;
         return extension;
         default: return c;
      }
   }
}
// 3.28†

// §4. Reporting Errors to the User.
// †4.3:
void err_print(char *s) {	// prints ‛‹.›’ and location of error message
   printf(*s ≡ '!'? "\n%s": "%s", s);
   if (web_file_open) {
   // †4.4: Print error location based on input buffer
   // The error locations can be indicated by using the global variables ≪loc≫, ≪cur_line≫, ≪cur_file_name≫ and ≪changing≫,
   // which tell respectively the first unlooked-at position in ≪buffer≫, the current line number, the current file,
   // and whether the current line is from ≪change_file≫ or ≪cur_file≫.
   // This routine should be modified on systems whose standard text editor has special line-numbering conventions. ⁅28⁆
      if (changing ∧ include_depth ≡ change_depth) printf(". (l. %d of change file)\n", change_line);
      else if (include_depth ≡ 0) printf(". (l. %d)\n", cur_line);
      else printf(". (l. %d of include file %s)\n", cur_line, cur_file_name);
      char *l = loc ≥ limit? limit: loc;	// pointer into ≪buffer≫
      if (l > buffer) {
         for (char *k = buffer; k < l; k↑) putchar(*k ≡ '\t'? ' ': *k);	// print the characters already read
         putchar('\n');
         for (char *k = buffer; k < l; k↑) putchar(' ');	// space out the next line
      }
      for (char *k = l; k < limit; k↑) putchar(*k);	// print the part not yet read
      if (*limit ≡ '|') putchar('|');		// end of ‹C99› text in section names
      putchar(' ');				// to separate the message from future asterisks
   // 4.4†
   }
   update_terminal(), mark_error();
}

// 4.3†4.6:
// Some implementations may wish to pass the ≪history≫ value to the operating system so that it can be used to govern whether or not other programs are started.
// Here, for instance, we pass the operating system a status of 0 if and only if only harmless messages were printed. ⁅29⁆
int wrap_up(void) {
   putchar('\n');
   if (show_stats) print_stats();	// print statistics about memory usage
// †4.7: Print the job ≪history≫
   switch (history) {
      case spotless:
         if (show_happiness) printf("(No errors were found.)\n");
      break;
      case harmless_message: printf("(Did you see the warning message above?)\n"); break;
      case error_message: printf("(Pardon me, but I think I spotted something wrong.)\n"); break;
      case fatal_message: printf("(That was a fatal error, my friend.)\n"); break;
   }	// there are no other cases
// 4.7†
   return history > harmless_message;
}

// 4.6†4.9:
// The two parameters to ≪fatal≫ are strings that are essentially concatenated to print the final error message.
void fatal(char *s, char *t) {
   if (*s ≠ '\0') printf(s);
   err_print(t), history = fatal_message, exit(wrap_up());
}

// 4.9†4.10:
// An overflow stop occurs if ≪CWEB≫'s tables aren't large enough.
void overflow(char *t) { printf("\n! Sorry, %s capacity exceeded", t), fatal("", ""); }	// ⁅30⁆

// 4.10†4.11:
// Sometimes the program's behavior is far different from what it should be,
// and ≪CWEB≫ prints an error message that is really for the ≪CWEB≫ maintenance person, not the user.
// In such cases the program says ≪confusion("indication of where we are")≫.
#define confusion(s) fatal("! This can't happen: ", s)	// ⁅31⁆
// 4.11†

// §5. Command Line Arguments.
// †5.4:
void scan_args(void) {
   boolean found_web = 0, found_change = 0, found_out = 0;	// have these names been seen?
   while (↓argc > 0) {
      if ((**↑argv ≡ '-' ∨ **argv ≡ '+') ∧ *(*argv + 1)) {
      // †5.8: Handle flag argument
         boolean flag_change = **argv ≠ '-';
         for (char *dot_pos = *argv + 1; *dot_pos > '\0'; dot_pos↑) flags[*dot_pos] = flag_change;
      // 5.8†
      } else {
         char *name_pos = *argv;	// file name beginning, sans directory
         char *dot_pos = NULL;	// position of ≪'.'≫ in the argument
         register char *s = name_pos;
         for (; *s ≠ '\0'; s↑) if (*s ≡ '.') dot_pos = s; else if (*s ≡ '/') dot_pos = NULL, name_pos = s + 1;
         if (!found_web) {
         // †5.5: Make ≪web_file_name≫, ≪tex_file_name≫, and ≪C_file_name≫
         // We use all of ≪*argv≫ for the ≪web_file_name≫ if there is a ≪'.'≫ in it, otherwise we add ≪".w"≫.
         // If this file can't be opened, we prepare an ≪alt_web_file_name≫ by adding ≪"web"≫ after the dot.
         // The other file names come from adding other things after the dot.
         // We must check that there is enough room in ≪web_file_name≫ and the other arrays for the argument.
            if (s - *argv > max_file_name_length - 5) LongFileName();	// Complain about argument length
            if (dot_pos ≡ NULL) sprintf(web_file_name, "%s.w", *argv);
            else strcpy(web_file_name, *argv), *dot_pos = 0;	// string now ends where the dot was
            sprintf(alt_web_file_name, "%s.web", *argv);
            sprintf(tex_file_name, "%s.tex", name_pos);	// strip off directory name
            sprintf(idx_file_name, "%s.idx", name_pos);
            sprintf(scn_file_name, "%s.scn", name_pos);
            sprintf(C_file_name, "%s.c", name_pos);
            found_web = 1;
         // 5.5†
         } else if (!found_change) {
         // †5.6: Make ≪change_file_name≫ from ≪fname≫
            if (strcmp(*argv, "-") ≡ 0) found_change = -1;
            else {
               if (s - *argv > max_file_name_length - 4) LongFileName();	// Complain about argument length
               if (dot_pos ≡ NULL) sprintf(change_file_name, "%s.ch", *argv); else strcpy(change_file_name, *argv);
               found_change = 1;
            }
         // 5.6†
         } else if (!found_out) {
         // †5.7: Override ≪tex_file_name≫ and ≪C_file_name≫
            if (s - *argv > max_file_name_length - 5) LongFileName();	// Complain about argument length
            if (dot_pos ≡ NULL)
               sprintf(tex_file_name, "%s.tex", *argv), sprintf(idx_file_name, "%s.idx", *argv),
               sprintf(scn_file_name, "%s.scn", *argv), sprintf(C_file_name, "%s.c", *argv);
            else {
               strcpy(tex_file_name, *argv), strcpy(C_file_name, *argv);
               if (flags['x'])	// indexes will be generated
                  *dot_pos = 0,
                  sprintf(idx_file_name, "%s.idx", *argv),
                  sprintf(scn_file_name, "%s.scn", *argv);
            }
            found_out = 1;
         // 5.7†
         } else Usage();	// Print usage error message and quit
      }
   }
   if (!found_web) Usage();	// Print usage error message and quit
   if (found_change ≤ 0) strcpy(change_file_name, "/dev/null");
}

// 5.4†5.9: Print usage error message and quit
// Editor's Note:
// ∙	This was orginally a multiply-used module.
inline void Usage(void) {
   if (program ≡ ctangle) fatal("! Usage: ctangle [options] webfile[.w] [{changefile[.ch]|-} [outfile[.c]]]\n", "");	// ⁅32⁆
   else fatal("! Usage: cweave [options] webfile[.w] [{changefile[.ch]|-} [outfile[.tex]]]\n", "");
}

// 5.9†5.10 [3]: Complain about argument length
// Editor's Note:
// ∙	This was orginally a multiply-used module.
inline void LongFileName(void) { fatal("! Filename too long\n", *argv); }	// ⁅33⁆
// 5.10†

// §6. Output.
// †6.3:
// The ≪update_terminal()≫ procedure is called when we want to make sure
// that everything we have output to the terminal so far has actually left the computer's internal buffers and been sent. ⁅34⁆
#define update_terminal() fflush(stdout)	// empty the terminal output buffer

// 6.3†6.4:
// Terminal output uses ≪putchar≫ and ≪putc≫ when we have to translate from ≪CWEB≫'s code into the external character code,
// and ≪printf≫ when we just want to print strings.
// Several macros make other kinds of output convenient. ⁅35⁆
#define new_line() putchar('\n')
#define putxchar putchar
#define term_write(a, b) fflush(stdout), fwrite(a, sizeof(char), b, stdout)
#define C_printf(c, a) fprintf(C_file, c, a)
#define C_putc(c) putc(c, C_file)	// isn't ‹C99› wonderfully consistent?

// 6.4†6.5:
// Editor's Note:
// ∙	These routines were originally declared here (with legacy declarations), since pre-C99 compilers did not standardize the header file.
// extern size_t strlen(const char *S);					// the length of string ≪S≫.
// extern int strcmp(const char *S0, const char *S1);			// compare strings ≪S0≫ and ≪S1≫ lexicographically.
// extern char *strcpy(char *AdS, char *DeS);				// copy string ≪DeS≫ to ≪AdS≫ and return the ≪AdS≫.
// extern int strncmp(const char *S0, const char *S1, size_t N);	// compare up to ≪N≫ string characters of ≪S0≫ and ≪S1≫.
// extern char *strncpy(char *AdS, char *DeS, size_t N);		// copy up to ≪N≫ string characters of ≪DeS≫ to ≪AdS≫ and return ≪AdS≫.
#include <string.h>
// 6.5†

// §7. Index.
// †7.1:
//	⇔	Ambiguous prefix ...		― ⁅24⁆
//	↔	ASCII code dependencies		― ⁅03⁆
//	⇔	Cannot open change file		― ⁅15⁆
//	⇔	Cannot open input file		― ⁅14⁆
//	⇔	Cannot open output file		― ⁅02⁆
//	⇔	Change file ended...		― ⁅08⁆⁅09⁆⁅16⁆
//	⇔	Change file entry did not match	― ⁅22⁆
//	⇔	CWEB file ended...		― ⁅12⁆
//	⇔	Filename too long		― ⁅33⁆
//	↔	high-bit character handling	― ⁅23⁆
//	⇔	Hmm... n of the preceding...	― ⁅11⁆
//	⇔	Include file name ...		― ⁅18⁆⁅20⁆⁅21⁆
//	⇔	Input line too long		― ⁅06⁆
//	⇔	Missing @x...			― ⁅07⁆
//	⇔	New name extends...		― ⁅26⁆
//	⇔	New name is a prefix...		― ⁅25⁆
//	⇔	Section name incompatible...	― ⁅27⁆
//	⇔	Sorry, capacity exceeded	― ⁅30⁆
//	↔	system dependencies		― ⁅00⁆⁅01⁆⁅04⁆⁅05⁆⁅13⁆⁅28⁆⁅29⁆⁅34⁆⁅35⁆
//	⇔	This can't happen		― ⁅31⁆
//	⇔	Too many nested includes	― ⁅19⁆
//	⇔	Usage:				― ⁅32⁆
//	⇔	Where is the match...		― ⁅10⁆⁅17⁆
// 7.1†
