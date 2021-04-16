// This file is part of CWEB.
// This program by Silvio Levy and Donald E. Knuth
// is based on a program by Knuth.
// It is distributed WITHOUT ANY WARRANTY, express or implied.
// Version 3.64 --- February 2002
// (same as Version 3.5 except for minor corrections)
// (also quotes backslashes in file names of #line directives)

// Copyright (C) 1987, 1990, 1993, 2000 Silvio Levy and Donald E. Knuth

// Permission is granted to make and distribute verbatim copies of this
// document provided that the copyright notice and this permission notice
// are preserved on all copies.

// Permission is granted to copy and distribute modified versions of this
// document under the conditions for verbatim copying, provided that the
// entire resulting derived work is given a different name and distributed
// under the terms of a permission notice identical to this one.

// Here is TeX material that gets inserted after ‹input› cwebmac
// ‹def›‹hang›{‹hangindent› 3em‹indent›‹ignorespaces›}
// ‹def›‹pb›{$‹|›…‹|›$}	%% C brackets (|...|)

// ‹def›‹title›{CTANGLE (Version 3.64)}
// ‹def›‹topofcontents›{
//    ‹null›‹vfill›
//    ‹centerline›{‹titlefont› The {‹ttitlefont› CTANGLE} processor}
//    ‹vskip› 15pt
//    ‹centerline›{(Version 3.64)}
//    ‹vfill›
// }
// ‹def›‹botofcontents›{
//    ‹vfill›
//    ‹noindent›
//    Copyright ‹copyright› 1987, 1990, 1993, 2000 Silvio Levy and Donald E. Knuth
//    ‹bigskip›‹noindent›
//    Permission is granted to make and distribute verbatim copies of this document
//    provided that the copyright notice and this permission notice are preserved on all copies.
//    ‹smallskip›‹noindent›
//    Permission is granted to copy and distribute modified versions of this document under the conditions for verbatim copying,
//    provided that the entire resulting derived work is given a different name
//    and distributed under the terms of a permission notice identical to this one.
// }
// ‹pageno› = ‹contentspagenumber› ‹advance›‹pageno› by 1
// ‹let›‹maybe› = ‹iftrue›
// #format not_eq normal	// unreserve a C++ keyword

// §1. Introduction.
// †1.0.1:
// This is the ‹CTANGLE› program by Silvio Levy and Donald E. Knuth, based on ‹TANGLE› by Knuth.
// We are thankful to Nelson Beebe, Hans-Hermann Bode (to whom the ‹C++› adaptation is due),
// Klaus Guntermann, Norman Ramsey, Tomas Rokicki, Joachim Schnitter, Joachim Schrod, Lee Wittenberg, and others who have contributed improvements.

// The ‟banner line” defined here should be changed whenever ‹CTANGLE› is modified.
#define banner "This is CTANGLE (Version 3.64)\n"

// †3.1.1: Include files
#include <ctype.h>	// definition of ≪isalpha≫, ≪isdigit≫ and so on
#include <stdlib.h>	// definition of ≪exit≫
// 3.1.1†

// §Defines:
// #defines here
// Defines§

// §Include "Common.h":
// Common code for ‹CWEAVE› and ‹CTANGLE›
// Include "Common.h"§

// †1.1.1: Typedef declarations (1/2)
// We've already seen that the ≪byte_mem≫ array holds the names of identifiers, strings, and sections; the ≪tok_mem≫ array holds the replacement texts for sections.
// Allocation is sequential, since things are deleted only during Phase II, and only in a last-in-first-out manner.

// A «text» variable is a structure containing a pointer into ≪tok_mem≫, which tells where the corresponding text starts, and an integer ≪text_link≫,
// which, as we shall see later, is used to connect pieces of text that have the same name.
// All the «text»s are stored in the array ≪text_info≫, and we use a ≪text_pointer≫ variable to refer to them.

// The first position of ≪tok_mem≫ that is unoccupied by replacement text is called ≪tok_ptr≫, and the first unused location of ≪text_info≫ is called ≪text_ptr≫.
// Thus we usually have the identity ≪text_ptr→tok_start ≡ tok_ptr≫.

// If your machine does not support ≪unsigned char≫ you should change the definition of «eight_bits» to ≪unsigned short≫. ⁅00⁆
typedef struct text {
   eight_bits *tok_start;	// pointer into ≪tok_mem≫
   sixteen_bits text_link;	// relates replacement texts
} text, *text_pointer;

// 1.1.1†2.0.1: Typedef declarations (2/2)
// The output process uses a stack to keep track of what is going on at different ‟levels” as the sections are being written out.
// Entries on this stack have five parts:
// ∙	≪end_field≫ is the ≪tok_mem≫ location where the replacement text of a particular level will end;
// ∙	≪byte_field≫ is the ≪tok_mem≫ location from which the next token on a particular level will be read;
// ∙	≪name_field≫ points to the name corresponding to a particular level;
// ∙	≪repl_field≫ points to the replacement text currently being read at a particular level;
// ∙	≪section_field≫ is the section number, or zero if this is a macro.
// The current values of these five quantities are referred to quite frequently,
// so they are stored in a separate place instead of in the ≪stack≫ array.
// We call the current values ≪cur_end≫, ≪cur_byte≫, ≪cur_name≫, ≪cur_repl≫, and ≪cur_section≫.

// The global variable ≪stack_ptr≫ tells how many levels of output are currently in progress.
// The end of all output occurs when the stack is empty, i.e., when ≪stack_ptr ≡ stack≫.
typedef struct output_state {
   eight_bits *end_field;	// ending location of replacement text
   eight_bits *byte_field;	// present location within replacement text
   name_pointer name_field;	// ≪byte_start≫ index for text being output
   text_pointer repl_field;	// ≪tok_start≫ index for text being output
   sixteen_bits section_field;	// section number or zero if not a section
} output_state, *stack_pointer;

// 2.0.1†1.1.2: Global variables (1/13)
text text_info[max_texts];
text_pointer text_info_end = text_info + max_texts - 1;
text_pointer text_ptr;	// first unused position in ≪text_info≫
eight_bits tok_mem[max_toks];
eight_bits *tok_mem_end = tok_mem + max_toks - 1;
eight_bits *tok_ptr;	// first unused position in ≪tok_mem≫

// 1.1.2†1.2.1: Global variables (2/13)
// Replacement texts, which represent ‹C99› code in a compressed format, appear in ≪tok_mem≫ as mentioned above.
// The codes in these texts are called ‛tokens’; some tokens occupy two consecutive eight-bit byte positions, and the others take just one byte.

// If $p$ points to a replacement text, ≪p→tok_start≫ is the ≪tok_mem≫ position of the first eight-bit code of that text.
// If ≪p→text_link ≡ 0≫, this is the replacement text for a macro, otherwise it is the replacement text for a section.
// In the latter case ≪p→text_link≫ is either equal to ≪section_flag≫,
// which means that there is no further text for this section, or ≪p→text_link≫ points to a continuation of this replacement text;
// such links are created when several sections have ‹C99› texts with the same name, and they also tie together all the ‹C99› texts of unnamed sections.
// The replacement text pointer for the first unnamed section appears in ≪text_info→text_link≫, and the most recent such pointer is ≪last_unnamed≫.
#define section_flag max_texts	// final ≪text_link≫ in section replacement texts

text_pointer last_unnamed;	// most recent replacement text of unnamed section

// 1.2.1†2.0.2: Global variables (3/13)
// Editor's Note:
// ∙	These were orignally declared, via macros, as fields of a variable ≪cur_state≫ of type ≪output_state≫.
eight_bits *cur_end;		// current ending location in ≪tok_mem≫
eight_bits *cur_byte;		// location of next output byte in ≪tok_mem≫
name_pointer cur_name;		// pointer to current name being expanded
text_pointer cur_repl;		// pointer to current replacement text
sixteen_bits cur_section;	// current section number being expanded

output_state stack[stack_size + 1];		// info for non-current levels
stack_pointer stack_ptr;			// first unused location in the output state stack
stack_pointer stack_end = stack + stack_size;	// end of ≪stack≫

// 2.0.2†2.0.6: Global variables (4/13)
// The heart of the output procedure is the function ≪get_output≫, which produces the next token of output and sends it on to the lower-level function ≪out_char≫.
// The main purpose of ≪get_output≫ is to handle the necessary stacking and unstacking.
// It sends the value ≪section_number≫ if the next output begins or ends the replacement text of some section,
// in which case ≪cur_val≫ is that section's number (if beginning) or the negative of that value (if ending).
// (A section number of 0 indicates not the beginning or ending of a section, but a «#line» command.)
// And it sends the value ≪identifier≫ if the next output is an identifier, in which case ≪cur_val≫ points to that identifier name.
#define section_number 0x81	// code returned by ≪get_output≫ for section numbers
#define identifier 0x82		// code returned by ≪get_output≫ for identifiers

int cur_val;	// additional information corresponding to output token

// 2.0.6†2.1.2: Global variables (5/13)
// First, we want to make sure that the output has spaces and line breaks in the right places
// (e.g., not in the middle of a string or a constant or an identifier, not at a ‛‹@&›’ position where quantities are being joined together,
// and certainly after an ‹=› because the ‹C99› compiler thinks ‹=-› is ambiguous).

// The output process can be in one of following states:
// ∙	≪num_or_id≫ means that the last item in the buffer is a number or identifier,
//	hence a blank space or line break must be inserted if the next item is also a number or identifier.
// ∙	≪unbreakable≫ means that the last item in the buffer was followed by the ‹@&› operation that inhibits spaces between it and the next item.
// ∙	≪verbatim≫ means we're copying only character tokens, and that they are to be output exactly as stored.
//	This is the case during strings, verbatim constructions and numerical constants.
// ∙	≪post_slash≫ means we've just output a slash.
// ∙	≪normal≫ means none of the above.
// Furthermore, if the variable ≪protect≫ is positive, newlines are preceded by a ‹\›'.
#define normal		0	// non-unusual state
#define num_or_id	1	// state associated with numbers and identifiers
#define post_slash	2	// state following a ‹/›
#define unbreakable	3	// state associated with ‹@&›
#define verbatim	4	// state in the middle of a string

eight_bits out_state;	// current status of partial output
boolean protect;	// should newline characters be quoted?

// 2.1.2†2.1.4: Global variables (6/13)
// Second, we have modified the original ‹TANGLE› so that it will write output on multiple files.
// If a section name is introduced in at least one place by ‹@(› instead of ‹@<›, we treat it as the name of a file.
// All these special sections are saved on a stack, ≪output_files≫.
// We write them out after we've done the unnamed section.
#define max_files 0x100
name_pointer output_files[max_files];
name_pointer *cur_out_file, *end_output_files, *an_output_file;
char cur_section_name_char;	// is it ≪'<'≫ or ≪'('≫
char output_file_name[longest_name];	// name of the file

// 2.1.4†2.2.5: Global variables (7/13)
boolean output_defs_seen = 0;

// 2.2.5†2.2.11: Global variables (8/13)
// When an identifier is output to the ‹C99› file, characters in the range 0x80 ― 0xff must be changed into something else, so the ‹C99› compiler won't complain.
// By default, ‹CTANGLE› converts the character with code $16x + y$ to the three characters ‛‹X›xy’, but a different transliteration table can be specified.
// Thus a German might want ≪_ grűun _≫ to appear as a still readable ‹gruen›.
// This makes debugging a lot less confusing.
#define translit_length 10

char translit[0x80][translit_length];

// 2.2.11†3.0.2: Global variables (9/13)
// Control codes in ‹CWEB› begin with ‛‹@›’, and the next character identifies the code.
// Some of these are of interest only to ‹CWEAVE›, so ‹CTANGLE› ignores them;
// the others are converted by ‹CTANGLE› into internal code numbers by the ≪ccode≫ table below.
// The ordering of these internal code numbers has been chosen to simplify the program logic;
// larger numbers are given to the control codes that denote more significant milestones.
#define ignore			0x00	// control code of no interest to ‹CTANGLE›
#define ord			0xc2	// control code for ‛‹@'›’
#define control_text		0xc3	// control code for ‛‹@t›’, ‛‹@^›’, etc.
#define translit_code		0xc4	// control code for ‛‹@l›’
#define output_defs_code	0xc5	// control code for ‛‹@h›’
#define format_code		0xc6	// control code for ‛‹@f›’
#define definition		0xc7	// control code for ‛‹@d›’
#define begin_C			0xc8	// control code for ‛‹@c›’
#define section_name		0xc9	// control code for ‛‹@<›’
#define new_section		0xca	// control code for ‛‹@ ›’ and ‛‹@*›’

eight_bits ccode[0x100];	// meaning of a char following ‹@›

// 3.0.2†3.0.5: Global variables (10/13)
// The ≪skip_comment≫ procedure reads through the input at somewhat high speed in order to pass over comments, which ‹CTANGLE› does not transmit to the output.
// If the comment is introduced by ‹/*›, ≪skip_comment≫ proceeds until finding the end-comment token ‹*/› or a newline;
// in the latter case ≪skip_comment≫ will be called again by ≪get_next≫, since the comment is not finished.
// This is done so that each newline in the ‹C99› part of a section is copied to the output;
// otherwise the «#line» commands inserted into the ‹C99› file by the output routines become useless.
// On the other hand, if the comment is introduced by ‹//› (i.e., if it is a ‹C++›/ ‟short comment”), it always is simply delimited by the next newline.
// The boolean argument ≪is_long_comment≫ distinguishes between the two types of comments.

// If ≪skip_comment≫ comes to the end of the section, it prints an error message.
// No comment, long or short, is allowed to contain ‛‹@ ›’ or ‛‹@*›’.
boolean comment_continues = 0;	// are we scanning a comment?

// 3.0.5†3.1.0: Global variables (11/13)
#define constant 0x03

name_pointer cur_section_name;	// name of section just scanned
int no_where;	// suppress ≪print_where≫?

// 3.1.0†3.2.1: Global variables (12/13)
// The rules for generating the replacement texts corresponding to macros and
// ‹C99› texts of a section are almost identical; the only differences are that
// ∙ a)	Section names are not allowed in macros;
//	in fact, the appearance of a section name terminates such macros and denotes the name of the current section.
// ∙ b)	The symbols ‹@d› and ‹@f› and ‹@c› are not allowed after section names, while they terminate macro definitions.
// ∙ c)	Spaces are inserted after right parentheses in macros, because the ANSI ‹C99› preprocessor sometimes requires it.
// Therefore there is a single procedure ≪scan_repl≫ whose parameter ≪t≫ specifies either ≪macro≫ or ≪section_name≫.
// After ≪scan_repl≫ has acted, ≪cur_text≫ will point to the replacement text just generated, and ≪next_control≫ will contain the control code that terminated the activity.
#define macro 0x00
inline void app_repl(eight_bits c) {
   if (tok_ptr ≡ tok_mem_end) overflow("token");
   *tok_ptr↑ = c;
}

text_pointer cur_text;	// replacement text formed by ≪scan_repl≫
eight_bits next_control;

// 3.2.1†3.3.1: Global variables (13/13)
// The ≪scan_section≫ procedure starts when ‛‹@ ›’ or ‛‹@*›’ has been sensed in the input, and it proceeds until the end of that section.
// It uses ≪section_count≫ to keep track of the current section number; with luck, ‹CWEAVE› and ‹CTANGLE› will both assign the same numbers to sections.
extern sixteen_bits section_count;	// the current section number
// 3.3.1†

// 1.0.1†1.0.2: Predeclaration of procedures (1/6)
// Editor's Note:
// ∙	These routines were originally declared here (with legacy declarations), since pre-C99 compilers did not standardize the header file.
// extern size_t strlen(const char *S);					// the length of string ≪S≫.
// extern int strcmp(const char *S0, const char *S1);			// compare strings ≪S0≫ and ≪S1≫ lexicographically.
// extern char *strcpy(char *AdS, char *DeS);				// copy string ≪DeS≫ to ≪AdS≫ and return the ≪AdS≫.
// extern int strncmp(const char *S0, const char *S1, size_t N);	// compare up to ≪N≫ string characters of ≪S0≫ and ≪S1≫.
// extern char *strncpy(char *AdS, char *DeS, size_t N);		// copy up to ≪N≫ string characters of ≪DeS≫ to ≪AdS≫ and return ≪AdS≫.
#include <string.h>

// †2.2.1: Predeclaration of procedures (2/6)
// Here then is the routine that does the output.
void phase_two(void);

// 2.2.1†2.2.6: Predeclaration of procedures (3/6)
void output_defs(void);

// 2.2.6†2.2.8: Predeclaration of procedures (4/6)
// A many-way switch is used to send the output.
// Note that this function is not called if ≪out_state ≡ verbatim≫,
// except perhaps with arguments ≪'\n'≫ (protect the newline), ≪string≫ (end the string), or ≪constant≫ (end the constant).
static void out_char(eight_bits c);

// 2.2.8†3.3.9: Predeclaration of procedures (5/6)
void phase_one(void);

// 3.3.9†3.3.11: Predeclaration of procedures (6/6)
// Only a small subset of the control codes is legal in limbo, so limbo processing is straightforward.
void skip_limbo(void);
// 3.3.11†1.0.3:
// ‹CTANGLE› has a fairly straightforward outline.
// It operates in two phases: First it reads the source file, saving the ‹C99› code in compressed form; then it shuffles and outputs the code.

// Please read the documentation for ‹common›, the set of routines common to ‹CTANGLE› and ‹CWEAVE›, before proceeding further.
int main(int ac, char **av) {
   argc = ac, argv = av, program = ctangle;
// †1.1.3: Set initial values (1/7)
   text_info→tok_start = tok_ptr = tok_mem, text_ptr = text_info + 1, text_ptr→tok_start = tok_mem;
// this makes replacement text 0 of length zero
// 1.1.3†1.1.5: Set initial values (2/7)
   name_dir→equiv = (char *)text_info;	// the undefined section has no replacement text
// 1.1.5†1.2.2: Set initial values (3/7)
   last_unnamed = text_info, text_info→text_link = 0;
// 1.2.2†2.1.5: Set initial values (4/7)
// We make ≪end_output_files≫ point just beyond the end of ≪output_files≫.
// The stack pointer ≪cur_out_file≫ starts out there.
// Every time we see a new file, we decrement ≪cur_out_file≫ and then write it in.
   cur_out_file = end_output_files = output_files + max_files;
// 2.1.5†2.2.12: Set initial values (5/7)
   for (int i = 0; i < 0x80; i↑) sprintf(translit[i], "X%02X", (unsigned)(0x80 + i));
// 2.2.12†3.0.3: Set initial values (6/7)
   for (int c = 0; c < 0x100; c↑) ccode[c] = ignore;	// ≪c≫ must be ≪int≫ so the ≪for≫ loop will end
   ccode[' '] = ccode['\t'] = ccode['\n'] = ccode['\v'] = ccode['\r'] = ccode['\f'] = ccode['*'] = new_section;
   ccode['@'] = '@', ccode['='] = string;
   ccode['d'] = ccode['D'] = definition;
   ccode['f'] = ccode['F'] = ccode['s'] = ccode['S'] = format_code;
   ccode['c'] = ccode['C'] = ccode['p'] = ccode['P'] = begin_C;
   ccode['^'] = ccode[':'] = ccode['.'] = ccode['t'] = ccode['T'] = ccode['q'] = ccode['Q'] = control_text;
   ccode['h'] = ccode['H'] = output_defs_code;
   ccode['l'] = ccode['L'] = translit_code;
   ccode['&'] = join;
   ccode['<'] = ccode['('] = section_name;
   ccode['\''] = ord;
// 3.0.3†3.1.10: Set initial values (7/7)
// Section names are placed into the ≪section_text≫ array with consecutive spaces, tabs, and carriage-returns replaced by single spaces.
// There will be no spaces at the beginning or the end. (We set ≪section_text[0]=' '≫ to facilitate this,
// since the ≪section_lookup≫ routine uses ≪section_text[1]≫ as the first character of the name.)
   section_text[0] = ' ';
// 3.1.10†
   common_init();
   if (show_banner) printf(banner);	// print a ‟banner line”
   phase_one();		// read all the user's text and compress it into ≪tok_mem≫
   phase_two();		// output the contents of the compressed tables
   return wrap_up();	// and exit gracefully
}

// 1.0.3†1.0.4:
// The following parameters were sufficient in the original ‹TANGLE› to handle ‹TeX›, so they should be sufficient for most applications of ‹CTANGLE›.
// If you change ≪max_bytes≫, ≪max_names≫, or ≪hash_size≫ you should also change them in the file ≪"common.w"≫.
#define max_bytes 90000		// the number of bytes in identifiers, index entries, and section names; used in ≪"common.w"≫
#define max_toks 270000		// number of bytes in compressed ‹C99› code
#define max_names 4000		// number of identifiers, strings, section names; must be less than 10240; used in ≪"common.w"≫
#define max_texts 2500		// number of replacement texts, must be less than 10240
#define hash_size 353		// should be prime; used in ≪"common.w"≫
#define longest_name 10000	// section names and strings shouldn't be longer than this
#define stack_size 50		// number of simultaneous levels of macro expansion
#define buf_size 100		// for ‹CWEAVE› and ‹CTANGLE›

// 1.0.4†1.0.5:
// The next few sections contain stuff from the file ≪"common.w"≫ that must be included in both ≪"ctangle.w"≫ and ≪"cweave.w"≫.
// It appears in file ≪"Common.h"≫, which needs to be updated when ≪"common.w"≫ changes.
#include "Common.h"
// 1.0.5†

// ‡1.1. Data Structures Exclusive to ≪_ CTANGLE _≫.
// †1.1.4:
// If ≪p≫ is a pointer to a section name, ≪p→equiv≫ is a pointer to its replacement text, an element of the array ≪text_info≫.
#define equiv equiv_or_xref	// info corresponding to names

// 1.1.4†1.1.6:
// Here's the procedure that decides whether a name of length ≪l≫ starting at position ≪first≫ equals the identifier pointed to by ≪p≫:

// (#) The original declaration int name_match(name_pointer p, char *first, int l); disagrees with that in {common,cweave}.c.
// p points to the proposed match, first is the position of the first character of the string and l is the length of the identifier.
int names_match(name_pointer p, char *first, int l, eight_bits t) { return length(p) = l ∧ strncmp(first, p→byte_start, l) ≡ 0; }

// 1.1.6†1.1.7:
// The common lookup routine refers to separate routines ≪init_node≫ and ≪init_p≫ when the data structure grows.
// Actually ≪init_p≫ is called only by ‹CWEAVE›, but we need to declare a dummy version so that the loader won't complain of its absence.
void init_node(name_pointer node) { node→equiv = (char *)text_info; }
void init_p(name_pointer p, eight_bits t) { }	// (#) The original declaration void init_p(void); disagrees with that for CWeave.c.
// 1.1.7†

// ‡1.2. Tokens.
// †1.2.3:
// If the first byte of a token is less than ≪0x80≫, the token occupies a single byte.
// Otherwise we make a sixteen-bit token by combining two consecutive bytes ≪a≫ and ≪b≫.
// If ≪0x80 ≤ a < 0xa8≫, then ≪(a - 0x80)×2⁸ + b≫ points to an identifier;
// if ≪0xa8 ≤ a < 0xd0≫, then ≪(a - 0xa8)×2⁸ + b≫ points to a section name
// (or, if it has the special value ≪output_defs_flag≫, to the area where the preprocessor definitions are stored);
// and if ≪0xd0 ≤ a < 0x100≫, then ≪(a - 0xd0)×2⁸ + b≫ is the number of the section in which the current replacement text appears.

// Codes less than ≪0x80≫ are 7-bit ≪char≫ codes that represent themselves.
// Some of the 7-bit codes will not be present, however, so we can use them for special purposes.
// The following symbolic names are used:
// ∙	≪join≫ denotes the concatenation of adjacent items with no space or line breaks allowed between them (the ‹@&› operation of ‹CWEB›).
// ∙	≪string≫ denotes the beginning or end of a string, verbatim construction or numerical constant. ⁅01⁆
#define string 0x02	// takes the place of extended ASCII \char2
#define join 0x7f	// takes the place of ASCII delete
#define output_defs_flag (2*0x2800 - 1)

// 1.2.3†1.2.4:
// The following procedure is used to enter a two-byte value into ≪tok_mem≫ when a replacement text is being generated.
void store_two_bytes(sixteen_bits x) {
   if (tok_ptr + 2 > tok_mem_end) overflow("token");
   *tok_ptr↑ = x ⊃ 8;	// store high byte
   *tok_ptr↑ = x&0xff;	// store low byte
}
// 1.2.4†

// §2. Stacks for Output.
// †2.0.4:
// When the replacement text for name ≪p≫ is to be inserted into the output, the following subroutine is called to save the old level of output and get the new one going.

// We assume that the ‹C99› compiler can copy structures. ⁅02⁆
void push_level(name_pointer p) {	// suspends the current level
   if (stack_ptr ≡ stack_end) overflow("stack");
   *stack_ptr↑ = (output_state){
      .end_field: cur_end, .byte_field: cur_byte, .name_field: cur_name, .repl_field: cur_repl, .section_field: cur_section
   }
   if (p ≠ NULL)	// ≪p ≡ NULL≫ means we are in ≪output_defs≫
      cur_name = p, cur_repl = (text_pointer)p→equiv, cur_byte = cur_repl→tok_start, cur_end = (cur_repl + 1)→tok_start, cur_section = 0;
}

// 2.0.4†2.0.5:
// When we come to the end of a replacement text, the ≪pop_level≫ subroutine does the right thing:
// It either moves to the continuation of this replacement text or returns the state to the most recently stacked level.
void pop_level(int flag) {	// do this when ≪cur_byte≫ reaches ≪cur_end≫
// ≪flag ≡ NULL≫ means we are in ≪output_defs≫
   if (flag ≠ NULL ∧ cur_repl→text_link < section_flag)	// link to a continuation
      cur_repl = cur_repl→text_link + text_info,		// stay on the same level
      cur_byte = cur_repl→tok_start, cur_end = (cur_repl + 1)→tok_start;
   else if (↓stack_ptr > stack)	// go down to the previous level
      cur_end = stack_ptr→end_field, cur_byte = stack_ptr→byte_field, cur_name = stack_ptr→name_field,
      cur_repl = stack_ptr→repl_field, cur_section = stack_ptr→section_field;
}

// 2.0.5†2.0.7:
// If ≪get_output≫ finds that no more output remains, it returns with ≪stack_ptr ≡ stack≫. ⁅03⁆
void get_output(void) {	// sends next token to ≪out_char≫
   sixteen_bits a;	// value of current byte
restart:
   if (stack_ptr ≡ stack) return;
   else if (cur_byte ≡ cur_end) {
      cur_val = -(int)cur_section;	// cast needed because of sign extension
      pop_level(1);
      if (cur_val ≡ 0) goto restart;
      out_char(section_number);
      return;
   }
   a = *cur_byte↑;
   if (out_state ≡ verbatim ∧ a ≠ string ∧ a ≠ constant ∧ a ≠ '\n') C_putc(a);	// a high-bit character can occur in a string
   else if (a < 0x80) out_char(a);	// one-byte token
   else {
      a = 0x100*(a - 0x80) + *cur_byte↑;
      switch (a/0x2800) {	// ≪0x2800 ≡ 0x100*(0xa8 - 0x80)≫
         case 0: cur_val = a, out_char(identifier); break;
         case 1:
            if (a ≡ output_defs_flag) output_defs();
            else {
            // †2.0.8: Expand section ≪a - 0x2800≫
            // The user may have forgotten to give any ‹C99› text for a section name, or the ‹C99› text may have been associated with a different name by mistake.
               a -= 0x2800;
               if ((a + name_dir)→equiv ≠ (char *)text_info) push_level(a + name_dir);
               else if (a ≠ 0) printf("\n! Not present: <"), print_section_name(a + name_dir), err_print(">");	// ⁅04⁆
            // 2.0.8†
               goto restart;
            }
         break;
         default:
            cur_val = a - 0x5000; if (cur_val > 0) cur_section = cur_val;
            out_char(section_number);
         break;
      }
   }
}
// 2.0.7†

// ‡2.1. Producing the Output.
// †2.1.1:
// The ≪get_output≫ routine above handles most of the complexity of output generation,
// but there are two further considerations that have a nontrivial effect on ‹CTANGLE›'s algorithms.

// 2.1.1†2.1.3:
// Here is a routine that is invoked when we want to output the current line.
// During the output process, ≪cur_line≫ equals the number of the next line to be output.
void flush_buffer(void) {	// writes one line to output file
   C_putc('\n');
   if (cur_line%100 ≡ 0 ∧ show_progress) {
      printf(".");
      if (cur_line%500 ≡ 0) printf("%d", cur_line);
      update_terminal();	// progress report
   }
   cur_line↑;
}
// 2.1.3†

// ‡2.2. The big Output Switch.
// †2.2.2:
void phase_two(void) {
   web_file_open = 0, cur_line = 1;
// †2.0.3: Initialize the output stacks
// To get the output process started, we will perform the following initialization steps.
// We may assume that ≪text_info→text_link≫ is nonzero, since it points to the ‹C99› text in the first unnamed section that generates code;
// if there are no such sections, there is nothing to output, and an error message will have been generated before we do any of the initialization.
   stack_ptr = stack + 1,
   cur_name = name_dir, cur_repl = text_info→text_link + text_info,
   cur_byte = cur_repl→tok_start, cur_end = (cur_repl + 1)→tok_start, cur_section = 0;
// 2.0.3†2.2.4: Output macro definitions if appropriate
// If a ‹@h› was not encountered in the input,
// we go through the list of replacement texts and copy the ones that refer to macros, preceded by the ‹#define› preprocessor command.
   if (!output_defs_seen) output_defs();
// 2.2.4†
   if (text_info→text_link ≡ 0 ∧ cur_out_file ≡ end_output_files) printf("\n! No program text was specified."), mark_harmless();	// ⁅05⁆
   else {
      if (cur_out_file ≡ end_output_files) {
         if (show_progress) printf("\nWriting the output file (%s):", C_file_name);
      } else {
         if (show_progress) printf("\nWriting the output files:"), printf(" (%s)", C_file_name), update_terminal();	// ⁅06⁆
         if (text_info→text_link ≡ 0) goto writeloop;
      }
      while (stack_ptr > stack) get_output();
      flush_buffer();
   writeloop:
   // †2.2.3: Write all the named output files
   // To write the named output files, we proceed as for the unnamed section.
   // The only subtlety is that we have to open each one.
      for (an_output_file = end_output_files; an_output_file > cur_out_file; ) {
         sprint_section_name(output_file_name, *↓an_output_file);
         fclose(C_file), C_file = fopen(output_file_name, "w"); if (C_file ≡ 0) fatal("! Cannot open output file:", output_file_name);	// ⁅07⁆
         printf("\n(%s)", output_file_name), update_terminal();
         cur_line = 1;
         stack_ptr = stack + 1;
         cur_name = *an_output_file, cur_repl = (text_pointer)cur_name→equiv;
         cur_byte = cur_repl→tok_start, cur_end = (cur_repl + 1)→tok_start;
         while (stack_ptr > stack) get_output();
         flush_buffer();
      }
   // 2.2.3†
      if (show_happiness) printf("\nDone.");
   }
}

// 2.2.2†2.2.7:
void output_defs(void) {
   push_level(NULL);
   for (cur_text = text_info + 1; cur_text < text_ptr; cur_text↑) if (cur_text→text_link ≡ 0) {	// ≪cur_text≫ is the text for a macro
      cur_byte = cur_text→tok_start, cur_end = (cur_text + 1)→tok_start;
      C_printf("%s", "#define ");
      out_state = normal;
      protect = 1;	// newlines should be preceded by ≪'\\'≫
      while (cur_byte < cur_end) {
         sixteen_bits a = *cur_byte↑;
         if (cur_byte ≡ cur_end ∧ a ≡ '\n') break;	// disregard a final newline
         else if (out_state ≡ verbatim ∧ a ≠ string ∧ a ≠ constant ∧ a ≠ '\n') C_putc(a);	// a high-bit character can occur in a string ⁅08⁆
         else if (a < 0x80) out_char(a);	// one-byte token
         else {
            a = 0x100*(a - 0x80) + *cur_byte↑;
            if (a < 0x2800) cur_val = a, out_char(identifier);	// ≪0x2800 ≡ 0x100*(0xa8 - 0x80)≫
            else if (a < 0x5000) confusion("macro defs have strange char");
            else cur_val = a - 0x5000, cur_section = cur_val, out_char(section_number);
         // no other cases
         }
      }
      protect = 0, flush_buffer();
   }
   pop_level(0);
}

// 2.2.7†2.2.9:
static void out_char(eight_bits cur_char) {
restart:
   switch (cur_char) {
      case '\n':
         if (protect ∧ out_state ≠ verbatim) C_putc(' ');
         if (protect ∨ out_state ≡ verbatim) C_putc('\\');
         flush_buffer(); if (out_state ≠ verbatim) out_state = normal;
      break;
   // †2.2.13: Case of an identifier
      case identifier:
         if (out_state ≡ num_or_id) C_putc(' ');
         for (char *j = (cur_val + name_dir)→byte_start, *k = (cur_val + name_dir + 1)→byte_start; j < k; j↑)
            if ((unsigned char)*j < 0x80) C_putc(*j);	// ⁅09⁆
            else C_printf("%s", translit[(unsigned char)*j - 0x80]);
         out_state = num_or_id;
      break;
   // 2.2.13†2.2.14: Case of a section number
      case section_number:
         if (cur_val > 0) C_printf("/*%d:*/", cur_val);
         else if (cur_val < 0) C_printf("/*:%d*/", -cur_val);
         else if (protect) {
            cur_byte += 4;	// skip line number and file name
            cur_char = '\n';
            goto restart;
         } else {
            sixteen_bits a = 0x100 * *cur_byte↑; a += *cur_byte↑;	// gets the line number
            C_printf("\n#line %d \"", a);	// ⁅10⁆
            cur_val = *cur_byte↑, cur_val = 0x100*(cur_val - 0x80) + *cur_byte↑;	// points to the file name
            for (char *j = (cur_val + name_dir)→byte_start, *k = (cur_val + name_dir + 1)→byte_start; j < k; j↑) {
               if (*j ≡ '\\' ∨ *j ≡ '"') C_putc('\\');
               C_putc(*j);
            }
            C_printf("%s", "\"\n");
         }
      break;
   // 2.2.14†2.2.10: Cases like ‹!=›
      case plus_plus: C_putc('+'), C_putc('+'), out_state = normal; break;
      case minus_minus: C_putc('-'), C_putc('-'), out_state = normal; break;
      case minus_gt: C_putc('-'), C_putc('>'), out_state = normal; break;
      case gt_gt: C_putc('>'), C_putc('>'), out_state = normal; break;
      case eq_eq: C_putc('='), C_putc('='), out_state = normal; break;
      case lt_lt: C_putc('<'), C_putc('<'), out_state = normal; break;
      case gt_eq: C_putc('>'), C_putc('='), out_state = normal; break;
      case lt_eq: C_putc('<'), C_putc('='), out_state = normal; break;
      case not_eq: C_putc('!'), C_putc('='), out_state = normal; break;
      case and_and: C_putc('&'), C_putc('&'), out_state = normal; break;
      case or_or: C_putc('|'), C_putc('|'), out_state = normal; break;
      case dot_dot_dot: C_putc('.'), C_putc('.'), C_putc('.'), out_state = normal; break;
      case colon_colon: C_putc(':'), C_putc(':'), out_state = normal; break;
      case period_ast: C_putc('.'), C_putc('*'), out_state = normal; break;
      case minus_gt_ast: C_putc('-'), C_putc('>'), C_putc('*'), out_state = normal; break;
   // 2.2.10†
      case '=': case '>': C_putc(cur_char), C_putc(' '), out_state = normal; break;
      case join: out_state = unbreakable; break;
      case constant:
         if (out_state ≡ verbatim) { out_state = num_or_id; break; }
         if (out_state ≡ num_or_id) C_putc(' ');
         out_state = verbatim;
      break;
      case string: out_state = out_state ≡ verbatim? normal: verbatim; break;
      case '/': C_putc('/'), out_state = post_slash; break;
      case '*':
         if (out_state ≡ post_slash) C_putc(' ');
      default:
         C_putc(cur_char), out_state = normal;
      break;
   }
}
// 2.2.9†

// §3. Introduction to the Input Phase.
// †3.0.1:
// We have now seen that ‹CTANGLE› will be able to output the full ‹C99› program, if we can only get that program into the byte memory in the proper format.
// The input process is something like the output process in reverse, since we compress the text as we read it in and we expand it as we write it out.

// There are three main input routines.
// The most interesting is the one that gets the next token of a ‹C99› text;
// the other two are used to scan rapidly past ‹TeX› text in the ‹CWEB› source code.
// One of the latter routines will jump to the next token that starts with ‛‹@›’, and the other skips to the end of a ‹C99› comment.

// 3.0.1†3.0.4:
// The ≪skip_ahead≫ procedure reads through the input at fairly high speed until finding the next non-ignorable control code, which it returns.
eight_bits skip_ahead(void) {	// skip to next control code
   while (1) {
      if (loc > limit ∧ get_line() ≡ 0) return new_section;
      *(limit + 1) = '@';
      for (; *loc ≠ '@'; loc↑);
      if (loc ≤ limit) {
         loc↑;
         eight_bits c = ccode[(eight_bits)*loc↑];	// control code found
         if (c ≠ ignore ∨ *(loc - 1) ≡ '>') return c;
      }
   }
}

// 3.0.4†3.0.6:
int skip_comment(boolean is_long_comment) {	// skips over comments
   while (1) {
      if (loc > limit) {
         if (!is_long_comment) return 0;
         else if (get_line()) return 1;
         else { err_print("! Input ended in mid-comment"); return 0; }	// ⁅11⁆
      }
      char c = *loc↑;	// the current character
      if (is_long_comment ∧ c ≡ '*' ∧ *loc ≡ '/') { loc↑; return 0; }
      else if (c ≡ '@') {
         if (ccode[(eight_bits)*loc] ≡ new_section) {
            err_print("! Section name ended in mid-comment"), loc↓;	// ⁅12⁆
            return 0;
         } else loc↑;
      }
   }
}
// 3.0.6†3.2.3: [4] Insert the line number into ≪tok_mem≫
// Here is the code for the line number: first a ≪sixteen_bits≫ equal to ≪0xd000≫; then the numeric line number; then a pointer to the file name.
// Editor's Note:
// ∙	This was orginally a multiply-used module.
inline void InsertLineNum(void) {
   store_two_bytes(0xd000);
   if (changing ∧ include_depth ≡ change_depth)	// correction made Feb 2017
      id_first = change_file_name, store_two_bytes((sixteen_bits)change_line);
   else
      id_first = cur_file_name, store_two_bytes((sixteen_bits)cur_line);
   id_loc = id_first + strlen(id_first);
   int a = id_lookup(id_first, id_loc, 0) - name_dir;
   app_repl(a/0x100 + 0x80), app_repl(a%0x100);
}
// 3.2.3†

// ‡3.1. Inputting the next token.
// †3.1.2:
// As one might expect, ≪get_next≫ consists mostly of a big switch that branches to the various special cases that can arise.
#define isxalpha(c) ((c) ≡ '_' ∨ (c) ≡ '$')	// non-alpha characters allowed in identifier
#define ishigh(c) ((unsigned char)(c) > 0x7f)	// ⁅13⁆

eight_bits get_next(void) {	// produces the next input token
   static int preprocessing = 0;
   while (1) {
      if (loc > limit) {
         if (preprocessing ∧ *(limit - 1) ≠ '\\') preprocessing = 0;
         if (get_line() ≡ 0) return new_section;
         else if (print_where ∧ !no_where) print_where = 0, InsertLineNum();	// Insert the line number into ≪tok_mem≫≫≫
         else return '\n';
      }
      eight_bits c = *loc;	// the current character
      if (comment_continues ∨ c ≡ '/' ∧ (*(loc + 1) ≡ '*' ∨ *(loc + 1) ≡ '/')) {
         comment_continues = skip_comment(comment_continues ∨ *(loc + 1) ≡ '*');	// scan to end of comment or newline
         if (comment_continues) return '\n'; else continue;
      }
      loc↑;
      if (xisdigit(c) ∨ c ≡ '.') {
      // †3.1.5: Get a constant
         id_first = loc - 1;
         if (*id_first ≡ '.' ∧ !xisdigit(*loc)) goto mistake;	// not a constant
         else if (*id_first ≡ '0' ∧ (*loc ≡ 'x' ∨ *loc ≡ 'X')) while (xisxdigit(*↑loc)) ;	// hex constant
         else {
            for (; xisdigit(*loc); loc↑);
            if (*loc ≡ '.') while (xisdigit(*↑loc)) ;
            if (*loc ≡ 'e' ∨ *loc ≡ 'E') {	// float constant
               if (*↑loc ≡ '+' ∨ *loc ≡ '-') loc↑;
               for (; xisdigit(*loc); loc↑);
            }
         }
         for (; *loc ≡ 'u' ∨ *loc ≡ 'U' ∨ *loc ≡ 'l' ∨ *loc ≡ 'L' ∨ *loc ≡ 'f' ∨ *loc ≡ 'F'; loc↑);
         id_loc = loc;
         return constant;
      // 3.1.5‡
      } else if (c ≡ '\'' ∨ c ≡ '"' ∨ c ≡ 'L' ∧ (*loc= = '\'' ∨ *loc ≡ '"')) {
      // †3.1.6: Get a string
      // ‹C99› strings and character constants, delimited by double and single quotes, respectively,
      // can contain newlines or instances of their own delimiters if they are protected by a backslash.
      // We follow this convention, but do not allow the string to be longer than ≪longest_name≫.
         char delim = c;	// what started the string
         id_first = section_text + 1, id_loc = section_text, *↑id_loc = delim;
         if (delim ≡ 'L') *↑id_loc = delim = *loc↑;	// wide character constant
         while (1) {
            if (loc ≥ limit) {
               if (*(limit - 1) ≠ '\\') { err_print("! String didn't end"), loc = limit; break; }	// ⁅14⁆
               else if (get_line() ≡ 0) { err_print("! Input ended in middle of string"), loc = buffer; break; }	// ⁅15⁆
               else if (↑id_loc ≤ section_text_end) *id_loc = '\n';	// will print as ‹"\\\n"›
            }
            if ((c = *loc↑) ≡ delim) {
               if (↑id_loc ≤ section_text_end) *id_loc = c;
               break;
            }
            if (c ≡ '\\') {
               if (loc ≥ limit) continue;
               if (↑id_loc ≤ section_text_end) *id_loc = '\\';
               c = *loc↑;
            }
            if (↑id_loc ≤ section_text_end) *id_loc = c;
         }
         if (id_loc ≥ section_text_end) printf("\n! String too long: "), term_write(section_text + 1, 25), err_print("...");	// ⁅16⁆
         id_loc↑;
         return string;
      // 3.1.6†
      } else if (isalpha(c) ∨ isxalpha(c) ∨ ishigh(c)) {
      // †3.1.4: Get an identifier
         id_first = ↓loc;
         while (isalpha(*↑loc) ∨ isdigit(*loc) ∨ isxalpha(*loc) ∨ ishigh(*loc));
         id_loc = loc;
         return identifier;
      // 3.1.4†
      } else if (c ≡ '@')
      // †3.1.7: Get control code and possible section name
      // After an ‹@› sign has been scanned, the next character tells us whether there is more work to do.
         switch (c = ccode[(eight_bits)*loc↑]) {
            case ignore: continue;
            case translit_code: err_print("! Use @l in limbo only"); continue;	// ⁅17⁆
            case control_text:
               while ((c = skip_ahead()) ≡ '@');
            // only ‹@@› and ‹@>› are expected
               if (*(loc - 1) ≠ '>') err_print("! Double @ should be used in control text");	// ⁅18⁆
            continue;
            case section_name: {
               cur_section_name_char = *(loc - 1);
            // †3.1.9: Scan the section name and make ≪cur_section_name≫ point to it
               char *k = section_text;	// pointer into ≪section_text≫
            // †3.1.11: Put section name into ≪section_text≫
               while (1) {
                  if (loc > limit ∧ get_line() ≡ 0) { err_print("! Input ended in section name"), loc = buffer + 1; break; }	// ⁅19⁆
                  c = *loc;
               // †3.1.12: If end of name or erroneous nesting, ≪break≫
                  if (c ≡ '@') {
                     c = *(loc + 1);
                     if (c ≡ '>') { loc += 2; break; }
                     else if (ccode[(eight_bits)c] ≡ new_section) { err_print("! Section name didn't end"); break; }	// ⁅20⁆
                     else if (ccode[(eight_bits)c] ≡ section_name) { err_print("! Nesting of section names not allowed"); break; }	// ⁅21⁆
                     *↑k = '@', loc↑;	// now ≪c ≡ *loc≫ again
                  }
               // 3.1.12†
                  loc↑; if (k < section_text_end) k↑;
                  if (xisspace(c)) {
                     c = ' '; if (*(k - 1) ≡ ' ') k↓;
                  }
                  *k = c;
               }
               if (k ≥ section_text_end)
                  printf("\n! Section name too long: "), term_write(section_text + 1, 25), printf("..."), mark_harmless();	// ⁅22⁆
               if (*k ≡ ' ' ∧ k > section_text) k↓;
            // 3.1.11†
               cur_section_name = k - section_text > 3 ∧ strncmp(k - 2, "...", 3) ≡ 0?
                  section_lookup(section_text + 1, k - 3, 1):	// 1 means is a prefix
                  section_lookup(section_text + 1, k, 0);
               if (cur_section_name_char ≡ '(') {
               // †2.1.6: If it's not there, add ≪cur_section_name≫ to the output file stack, or complain we're out of room
                  for (an_output_file = cur_out_file; an_output_file < end_output_files; an_output_file↑) if (*an_output_file ≡ cur_section_name) break;
                  if (an_output_file ≡ end_output_files)
                     if (cur_out_file > output_files) *↓cur_out_file = cur_section_name;
                     else overflow("output files");
               // 2.1.6†
               }
            // 3.1.9†
            }
            return section_name;
            case string: {
            // †3.1.13: Scan a verbatim string
            // At the present point in the program we have ≪*(loc-1) ≡ string≫; we set ≪id_first≫ to the beginning of the string itself,
            // and ≪id_loc≫ to its ending-plus-one location in the buffer.
            // We also set ≪loc≫ to the position just after the ending delimiter.
               id_first = loc↑, *(limit + 1) = '@', *(limit + 2) = '>';
               for (; *loc ≠ '@' ∨ *(loc + 1) ≠ '>'; loc↑);
               if (loc ≥ limit) err_print("! Verbatim string didn't end");	// ⁅23⁆
               id_loc = loc, loc += 2;
            // 3.1.13†
            }
            return string;
            case ord:
            // †3.1.8: Scan an ASCII constant
            // After scanning a valid ASCII constant that follows ‹@'›, this code plows ahead until it finds the next single quote.
            // (Special care is taken if the quote is part of the constant.)
            // Anything after a valid ASCII constant is ignored; thus, ‹@'\nopq'› gives the same result as ‹@'\n'›.
               id_first = loc;
               if (*loc ≡ '\\' ∧ *↑loc ≡ '\'') loc↑;
               while (*loc ≠ '\'') {
                  if (*loc ≡ '@') {
                     if (*(loc + 1) ≠ '@') err_print("! Double @ should be used in ASCII constant");	// ⁅24⁆
                     else loc↑;
                  }
                  if (↑loc > limit) { err_print("! String didn't end"), loc = limit - 1; break; }	// ⁅25⁆
               }
               loc↑;
            return ord;
            // 3.1.8†
            default: return c;
         }
      // 3.1.7†
      else if (xisspace(c)) {
         if (!preprocessing ∨ loc > limit) continue;	// we don't want a blank after a final backslash
         else return ' ';	// ignore spaces and tabs, unless preprocessing
      } else if (c ≡ '#' ∧ loc ≡ buffer + 1) preprocessing = 1;
   mistake:
   // †3.1.3: Compress two-symbol operator
   // The following code assigns values to the combinations
   //	‹++›, ‹--›, ‹->›, ‹>=›, ‹<=›, ‹==›, ‹<<›, ‹>>›, ‹!=›, ‹||› and ‹&&›,
   // and to the ‹C++› combinations
   //	‹...›, ‹::›, ‹.*› and ‹→*›.
   // The compound assignment operators (e.g., ‹+=›) are treated as separate tokens.
#define compress(c) if (loc↑ ≤ limit) return (c)
      switch (c) {
         case '+': switch (*loc) {
            case '+': compress(plus_plus); break;
         }
         break;
         case '-': switch (*loc) {
            case '-': compress(minus_minus); break;
            case '>': switch (*(loc + 1)) {
               case '*': loc↑; compress(minus_gt_ast); break;
               default: compress(minus_gt); break;
            }
            break;
         }
         break;
         case '.': switch (*loc) {
            case '*': compress(period_ast); break;
            case '.': switch (*(loc + 1)) {
               case '.': loc↑; compress(dot_dot_dot); break;
            }
            break;
         }
         break;
         case ':': switch (*loc) {
            case ':': compress(colon_colon); break;
         }
         break;
         case '=': switch (*loc) {
            case '=': compress(eq_eq); break;
         }
         break;
         case '>': switch (*loc) {
            case '=': compress(gt_eq); break;
            case '>': compress(gt_gt); break;
         }
         break;
         case '<': switch (*loc) {
            case '=': compress(lt_eq); break;
            case '<': compress(lt_lt);break;
         }
         break;
         case '&': switch (*loc) {
            case '&': compress(and_and); break;
         }
         break;
         case '|': switch (*loc) {
            case '|': compress(or_or); break;
         }
         break;
         case '!': switch (*loc) {
            case '=': compress(not_eq); break;
         }
         break;
      }
#undef compress
   // 3.1.3†
      return c;
   }
}
// 3.1.2†

// ‡3.2. Scanning a Macro Definition.
// †3.2.2:
void scan_repl(eight_bits t) {	// creates a replacement text
   sixteen_bits a;	// the current token
   if (t ≡ section_name) InsertLineNum();	// Insert the line number into ≪tok_mem≫≫≫
   while (1) switch (a = get_next()) {
   // †3.2.4: In cases that ≪a≫ is a non-≪char≫ token (≪identifier≫, ≪section_name≫, etc.),
   // either process it and change ≪a≫ to a byte that should be stored,
   // or ≪continue≫ if ≪a≫ should be ignored, or ≪goto done≫ if ≪a≫ signals the end of this replacement text
      case identifier:
         a = id_lookup(id_first, id_loc, 0) - name_dir, app_repl(a/0x100 + 0x80), app_repl(a%0x100);
      break;
      case section_name: {
         if (t ≠ section_name) goto done;
      // †3.2.5: Was an ‛@’ missed here?
         char *try_loc = loc;
         for (; *try_loc ≡ ' ' ∧ try_loc < limit; try_loc↑);
         if (*try_loc ≡ '+' ∧ try_loc < limit) try_loc↑;
         for (; *try_loc ≡ ' ' ∧ try_loc < limit; try_loc↑);
         if (*try_loc ≡ '=') err_print("! Missing `@ ' before a named section");	// ⁅26⁆
      // user who isn't defining a section should put newline after the name, as explained in the manual
      // 3.2.5†
         a = cur_section_name - name_dir, app_repl(a/0x100 + 0xa8), app_repl(a%0x100);
         InsertLineNum();	// Insert the line number into ≪tok_mem≫≫≫
      }
      break;
      case output_defs_code:
         if (t ≠ section_name) err_print("! Misplaced @h");	// ⁅27⁆
         else {
            output_defs_seen = 1;
            a = output_defs_flag, app_repl(a/0x100 + 0x80), app_repl(a%0x100);
            InsertLineNum();	// Insert the line number into ≪tok_mem≫≫≫
         }
      break;
      case constant: case string:
      // †3.2.6: Copy a string or verbatim construction or numerical constant
         app_repl(a);	// ≪string≫ or ≪constant≫
         while (id_first < id_loc) {	// simplify ‹@@› pairs
            if (*id_first ≡ '@') {
               if (*(id_first + 1) ≡ '@') id_first↑; else err_print("! Double @ should be used in string");	// ⁅28⁆
            }
            app_repl(*id_first↑);
         }
         app_repl(a);
      // 3.2.6†
      break;
      case ord: {
      // †3.2.7: Copy an ASCII constant
      // This section should be rewritten on machines that don't use ASCII code internally.  // ⁅29⁆
         int c = (eight_bits)*id_first;
         if (c ≡ '\\') {
            c = *↑id_first;
            if (c ≥ '0' ∧ c ≤ '7') {
               c -= '0';
               if (*(id_first + 1) ≥ '0' ∧ *(id_first + 1) ≤ '7') {
                  c = 010*c + *↑id_first - '0';
                  if (*(id_first + 1) ≥ '0' ∧ *(id_first + 1) ≤ '7' ∧ c < 0x20) c = 010*c + *↑id_first - '0';
               }
            } else switch (c) {
               case 't': c = '\t'; break;
               case 'n': c = '\n'; break;
               case 'b': c = '\b'; break;
               case 'f': c = '\f'; break;
               case 'v': c = '\v'; break;
               case 'r': c = '\r'; break;
               case 'a': c = '\7'; break;
               case '?': c = '?'; break;
               case 'x':
                  if (xisdigit(*(id_first + 1))) c = *↑id_first - '0';
                  else if (xisxdigit(*(id_first + 1))) c = toupper(*↑id_first) - 'A' + 10;
                  if (xisdigit(*(id_first + 1))) c = 0x10*c + *↑id_first - '0';
                  else if (xisxdigit(*(id_first + 1))) c = 0x10*c + toupper(*↑id_first) - 'A' + 10;
               break;
               case '\\': c = '\\'; break;
               case '\'': c = '\''; break;
               case '\"': c = '\"'; break;
               default: err_print("! Unrecognized escape sequence"); break;	// ⁅30⁆
            }
         }
      // at this point ≪c≫ should have been converted to its ASCII code number
         app_repl(constant);
         if (c ≥ 100) app_repl('0' + c/100);
         if (c ≥ 10) app_repl('0' + c/10%10);
         app_repl('0' + c%10), app_repl(constant);
      // 3.2.7†
      }
      break;
      case definition: case format_code: case begin_C:
         if (t ≠ section_name) goto done;
         err_print("! @d, @f and @c are ignored in C text");	// ⁅31⁆
      continue;
      case new_section: goto done;
   // 3.2.4†
      case ')':
         app_repl(a);
         if (t ≡ macro) app_repl(' ');
      break;
      default: app_repl(a); break;	// store ≪a≫ in ≪tok_mem≫
   }
done:
   next_control = (eight_bits)a;
   if (text_ptr > text_info_end) overflow("text");
   cur_text = text_ptr, (↑text_ptr)→tok_start = tok_ptr;
}
// 3.2.2†

// ‡3.3. Scanning a Section.
// †3.3.2:
// The body of ≪scan_section≫ is a loop where we look for control codes that are significant to ‹CTANGLE›:
// those that delimit a definition, the ‹C99› part of a module, or a new module.
void scan_section(void) {
   section_count↑, no_where = 1;
   if (*(loc - 1) ≡ '*' ∧ show_progress) printf("*%d", section_count), update_terminal();	// starred section
   next_control = 0;
   name_pointer p;	// section name for the current section
   while (1) {
   // †3.3.3: Skip ahead until ≪next_control≫ corresponds to ‹@d›, ‹@<›, ‹@ › or the like
   // At the top of this loop, if ≪next_control ≡ section_name≫, the section name has already been scanned (see ≪≪≪†3.1.7: Get control code and...≫≫≫).
   // Thus, if we encounter ≪next_control ≡ section_name≫ in the skip-ahead process, we should likewise scan the section name, so later processing will be the same in both cases.
      while (next_control < definition)	// ≪definition≫ is the lowest of the ‟significant” codes
         if ((next_control = skip_ahead()) ≡ section_name) loc -= 2, next_control = get_next();
   // 3.3.3†
      if (next_control ≡ definition) {	// ‹@d›
      // †3.3.4: Scan a definition
         while ((next_control = get_next()) ≡ '\n');	// allow newline before definition
         if (next_control ≠ identifier) { err_print("! Definition flushed, must start with identifier"); continue; }	// ⁅32⁆
         sixteen_bits a = id_lookup(id_first, id_loc, 0) - name_dir;	// token for left-hand side of definition
         app_repl(a/0x100 + 0x80), app_repl(a%0x100);	// append the lhs
         if (*loc ≠ '(')	// identifier must be separated from replacement text
            app_repl(string), app_repl(' '), app_repl(string);
         scan_repl(macro), cur_text→text_link = 0;	// ≪text_link ≡ 0≫ characterizes a macro
      // 3.3.4†
      } else if (next_control ≡ begin_C) { 	// ‹@c› or ‹@p›
         p = name_dir; break;
      } else if (next_control ≡ section_name) {	// ‹@<› or ‹@(›
         p = cur_section_name;
      // †3.3.5: If section is not being defined, ≪continue≫
      // If the section name is not followed by ‹=› or ‹+=›, no ‹C99› code is forthcoming: the section is being cited, not being defined.
      // This use is illegal after the definition part of the current section has started, except inside a comment,
      // but ‹CTANGLE› does not enforce this rule; it simply ignores the offending section name and everything following it, up to the next significant control code.
         while ((next_control = get_next()) ≡ '+');	// allow optional ‹+=›
         if (next_control ≡ '=' ∨ next_control ≡ eq_eq) break;
      // 3.3.5†
      } else return;	// ‹@ › or ‹@*›
   }
   no_where = print_where = 0;
// †3.3.6: Scan the ‹C99› part of the current section
// †3.3.7: Insert the section number into ≪tok_mem≫
   store_two_bytes((sixteen_bits)(0xd000 + section_count));	// ≪0xd000 ≡ 0x100*0xd0≫
// 3.3.7†
   scan_repl(section_name);	// now ≪cur_text≫ points to the replacement text
// †3.3.8: Update the data structure so that the replacement text is accessible
   if (p ≡ name_dir ∨ p ≡ 0)	// unnamed section, or bad section name
      (last_unnamed)→text_link = cur_text-text_info, last_unnamed = cur_text;
   else if (p→equiv ≡ (char *)text_info) p→equiv = (char *)cur_text;	// first section of this name
   else {
      text_pointer q = (text_pointer)p→equiv;	// text for the current section
      for (; q→text_link < section_flag; q = q→text_link + text_info);	// find end of list
      q→text_link = cur_text - text_info;
   }
   cur_text→text_link = section_flag;	// mark this replacement text as a nonmacro
// 3.3.8†
// 3.3.6†
}

// 3.3.2†3.3.10:
void phase_one(void) {
   phase = 1, section_count = 0, reset_input(), skip_limbo();
   while (!input_has_ended) scan_section();
   check_complete(), phase = 2;
}

// 3.3.10†3.3.12:
void skip_limbo(void) {
   while (1) {
      if (loc > limit ∧ get_line() ≡ 0) return;
      *(limit + 1) = '@';
      for (; *loc ≠ '@'; loc↑);
      if (loc↑ ≤ limit) {
         char c = *loc↑;
         if (ccode[(eight_bits)c] ≡ new_section) break;
         switch (ccode[(eight_bits)c]) {
            case translit_code:
            // †3.3.13: Read in transliteration of a character
               for (; xisspace(*loc) ∧ loc < limit; loc↑);
               loc += 3;
               if (loc > limit ∨ !xisxdigit(*(loc - 3)) ∨ !xisxdigit(*(loc - 2)) ∨ *(loc - 3) ≥ '0' ∧ *(loc - 3) ≤ '7' ∨ !xisspace(*(loc - 1)))
                  err_print("! Improper hex number following @l");	// ⁅33⁆
               else {
                  unsigned i; sscanf(loc - 3, "%x", &i);
                  for (; xisspace(*loc) ∧ loc < limit; loc↑);
                  char *beg = loc;
                  for (; loc < limit ∧ (xisalpha(*loc) ∨ xisdigit(*loc) ∨ *loc ≡ '_'); loc↑);
                  if (loc - beg ≥ translit_length) err_print("! Replacement string in @l too long");	// ⁅34⁆
                  else strncpy(translit[i - 0x80], beg, loc - beg), translit[i - 0x80][loc - beg] = '\0';
               }
            // 3.3.13†
            break;
            case format_code: case '@': break;
            case control_text:
               if (c ≡ 'q' ∨ c ≡ 'Q') {
                  while ((c = skip_ahead()) ≡ '@');
                  if (*(loc - 1) ≠ '>') err_print("! Double @ should be used in control text");	// ⁅35⁆
                  break;
               }
            default:
               err_print("! Double @ should be used in limbo");	// ⁅36⁆
            break;
         }
      }
   }
}

// 3.3.12†3.3.14:
// Because on some systems the difference between two pointers is a ≪long≫ but not an ≪int≫, we use ‹%ld› to print these quantities.
void print_stats(void) {
   printf("\nMemory usage statistics:\n");
   printf("%ld names (out of %ld)\n", (long)(name_ptr - name_dir), (long)max_names);
   printf("%ld replacement texts (out of %ld)\n", (long)(text_ptr - text_info), (long)max_texts);
   printf("%ld bytes (out of %ld)\n", (long)(byte_ptr - byte_mem), (long)max_bytes);
   printf("%ld tokens (out of %ld)\n", (long)(tok_ptr - tok_mem), (long)max_toks);
}
// 3.3.14†

// §4. Index.
// †4.0.1:
// Here is a cross-reference table for ‹CTANGLE›.
// All sections in which an identifier is used are listed with that identifier,
// except that reserved words are indexed only when they appear in format definitions, and the appearances of identifiers in section names are not indexed.
// Underlined entries correspond to where the identifier was declared.
// Error messages and a few other things like ‟ASCII code dependencies” are indexed here too.
//	→	ASCII code dependencies			―	⁅01⁆⁅29⁆
//	⇔	Cannot open output file			―	⁅07⁆
//	⇔	@d, @f and @c are ignored in C text	―	⁅31⁆
//	⇔	Definition flushed...			―	⁅32⁆
//	⇔	Double @ should be used...		―	⁅18⁆⁅24⁆⁅28⁆⁅35⁆⁅36⁆
//	→	high-bit character handling		―	⁅03⁆⁅08⁆⁅09⁆⁅13⁆
//	⇔	Improper hex number...			―	⁅33⁆
//	⇔	Input ended in mid-comment		―	⁅11⁆
//	⇔	Input ended in middle of string		―	⁅15⁆
//	⇔	Input ended in section name		―	⁅19⁆
//	↔	#line					―	⁅10⁆
//	⇔	Misplaced @h				―	⁅27⁆
//	⇔	Missing ‛@ ’...				―	⁅26⁆
//	⇔	Nesting of section names...		―	⁅21⁆
//	⇔	No program text...			―	⁅05⁆
//	⇔	Not present: <section name>		―	⁅04⁆
//	⇔	Replacement string in @l...		―	⁅34⁆
//	⇔	Section name didn't end			―	⁅20⁆
//	⇔	Section name ended in mid-comment	―	⁅12⁆
//	⇔	Section name too long			―	⁅22⁆
//	⇔	String didn't end			―	⁅14⁆⁅25⁆
//	⇔	String too long				―	⁅16⁆
//	→	system dependencies			―	⁅00⁆⁅02⁆
//	⇔	Unrecognized escape sequence		―	⁅30⁆
//	⇔	Use @l in limbo...			―	⁅17⁆
//	⇔	Verbatim string didn't end		―	⁅23⁆
//	⇔	Writing the output...			―	⁅06⁆
// 4.0.1†
