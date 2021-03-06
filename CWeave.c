// This file is part of CWEB.
// This program by Silvio Levy and Donald E. Knuth
// is based on a program by Knuth.
// It is distributed WITHOUT ANY WARRANTY, express or implied.
// Version 3.64 ― February 2002
// (essentially the same as version 3.6, which added
//  recently introduced features of standard C++ to version 3.4)
// (In November 2016 I made minor adjustments but changed no code − DEK)

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
// ‹def›‹pb›{$‹|›…‹|›$} %% C brackets (|...|)
//
// ‹def›‹title›{CWEAVE (Version 3.64)}
// ‹def›‹topofcontents›{
//    ‹null›‹vfill›
//    ‹centerline›{‹titlefont› The {‹ttitlefont› CWEAVE} processor}
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
// This is the ‹CWEAVE› program by Silvio Levy and Donald E. Knuth, based on ‹WEAVE› by Knuth.
// We are thankful to Steve Avery, Nelson Beebe, Hans-Hermann Bode (to whom the original ‹C++› adaptation is due),
// Klaus Guntermann, Norman Ramsey, Tomas Rokicki, Joachim Schnitter, Joachim Schrod, Lee Wittenberg,
// Saroj Mahapatra, Cesar Augusto Rorato Crusius, and others who have contributed improvements.

// The ‟banner line” defined here should be changed whenever ‹CWEAVE› is modified.
#define banner "This is CWEAVE (Version 3.64)\n"

// †1.3.2:
#include <ctype.h>	// definition of ≪isalpha≫, ≪isdigit≫ and so on
#include <stdlib.h>	// definition of ≪exit≫
// §Include "Common.h":
// ≪≪Include files≫≫
// Include "Common.h"§
// 1.3.2†

// §Defines:
// #defines here
// Defines§

// §Include "Common.h"
// ≪≪Common code for ‹CWEAVE› and ‹CTANGLE›≫≫
// Include "Common.h"§

// †1.1.3: Typedef declarations (1/4)
// The other large memory area in ‹CWEAVE› keeps the cross-reference data.
// All uses of the name ≪p≫ are recorded in a linked list beginning at ≪p→xref≫, which points into the ≪xmem≫ array.
// The elements of ≪xmem≫ are structures consisting of an integer, ≪num≫, and a pointer ≪xlink≫ to another element of ≪xmem≫.
// If ≪x = p→xref≫ is a pointer into ≪xmem≫, the value of ≪x→num≫ is either a section number where ≪p≫ is used,
// or ≪cite_flag≫ plus a section number where ≪p≫ is mentioned, or ≪def_flag≫ plus a section number where ≪p≫ is defined;
// and ≪x→xlink≫ points to the next such cross-reference for ≪p≫, if any.
// This list of cross-references is in decreasing order by section number.
// The next unused slot in ≪xmem≫ is ≪xref_ptr≫.
// The linked list ends at ≪&xmem[0]≫.

// The global variable ≪xref_switch≫ is set either to ≪def_flag≫ or to zero,
// depending on whether the next cross-reference to an identifier is to be underlined or not in the index.
// This switch is set to ≪def_flag≫ when ‹@!› or ‹@d› is scanned, and it is cleared to zero when the next identifier or index entry cross-reference has been made.
// Similarly, the global variable ≪section_xref_switch≫ is either ≪def_flag≫ or ≪cite_flag≫ or zero,
// depending on whether a section name is being defined, cited or used in ‹C99› text.
typedef struct xref_info {
   sixteen_bits num;		// section number plus zero or ≪def_flag≫
   struct xref_info *xlink;	// pointer to the previous cross-reference
} xref_info, *xref_pointer;
// 1.1.3†1.1.9: Typedef declarations (2/4)
// A third large area of memory is used for sixteen-bit ‛tokens’, which appear in short lists similar to the strings of characters in ≪byte_mem≫.
// Token lists are used to contain the result of ‹C99› code translated into ‹TeX› form; further details about them will be explained later.
// A ≪text_pointer≫ variable is an index into ≪tok_start≫.
typedef sixteen_bits token;
typedef token *token_pointer;
typedef token_pointer *text_pointer;
// 1.1.9†3.1.1: Typedef declarations (3/4)
// More specifically, a scrap is a structure consisting of a category ≪cat≫ and a ≪text_pointer≫ ≪trans≫, which points to the translation in ≪tok_start≫.
// When ‹C99› text is to be processed with the grammar above, we form an array ≪scrap_info≫ containing the initial scraps.
// Our production rules have the nice property that the right-hand side is never longer than the left-hand side.
// Therefore it is convenient to use sequential allocation for the current sequence of scraps.
// Five pointers are used to manage the parsing:
// ∙	≪pp≫ is a pointer into ≪scrap_info≫.
//	We will try to match the category codes ≪pp→cat, (pp + 1)→cat≫$, \,\, …\,$ to the left-hand sides of productions.
// ∙	≪scrap_base≫, ≪lo_ptr≫, ≪hi_ptr≫, and ≪scrap_ptr≫ are such that the current sequence of scraps
//	appears in positions ≪scrap_base≫ through ≪lo_ptr≫ and ≪hi_ptr≫ through ≪scrap_ptr≫, inclusive, in the ≪cat≫ and ≪trans≫ arrays.
//	Scraps located between ≪scrap_base≫ and ≪lo_ptr≫ have been examined, while those in positions ≪≥ hi_ptr≫ have not yet been looked at by the parsing process.
// Initially ≪scrap_ptr≫ is set to the position of the final scrap to be parsed, and it doesn't change its value.
// The parsing process makes sure that ≪lo_ptr ≥ pp + 3≫, since productions have as many as four terms, by moving scraps from ≪hi_ptr≫ to ≪lo_ptr≫.
// If there are fewer than ≪pp + 3≫ scraps left, the positions up to ≪pp + 3≫ are filled with blanks that will not match in any productions.
// Parsing stops when ≪pp ≡ lo_ptr + 1≫ and ≪hi_ptr ≡ scrap_ptr + 1≫.

// Since the ≪scrap≫ structure will later be used for other purposes, we declare its second element as a union.
typedef struct {
   eight_bits cat, mathness;
   union {
      text_pointer Trans;
   // †5.8: Rest of ≪trans_plus≫ union
      name_pointer Head;
   // 5.8†
   } trans_plus;
} scrap, *scrap_pointer;
// 3.1.1†3.3.2: Typedef declarations (4/4)
// The output process uses a stack to keep track of what is going on at different ‟levels” as the token lists are being written out.
// Entries on this stack have three parts:
// ∙	≪end_field≫ is the ≪tok_mem≫ location where the token list of a particular level will end;
// ∙	≪tok_field≫ is the ≪tok_mem≫ location from which the next token on a particular level will be read;
// ∙	≪mode_field≫ is the current mode, either ≪inner≫ or ≪outer≫.
// The current values of these quantities are referred to quite frequently, so they are stored in a separate place instead of in the ≪stack≫ array.
// We call the current values ≪cur_end≫, ≪cur_tok≫, and ≪cur_mode≫.

// The global variable ≪stack_ptr≫ tells how many levels of output are currently in progress.
// The end of output occurs when an ≪end_translation≫ token is found, so the stack is never empty except when we first begin the output process.
#define inner 0	// value of ≪mode≫ for ‹C99› texts within ‹TeX› texts
#define outer 1	// value of ≪mode≫ for ‹C99› texts in sections

typedef int mode;
typedef struct {
   token_pointer end_field;	// ending location of token list
   token_pointer tok_field;	// present location within token list
   boolean mode_field;		// interpretation of control tokens
} output_state, *stack_pointer;
// 3.3.2†

// †1.1.2: Global variables (1/24)
// We keep track of the current section number in ≪section_count≫, which is the total number of sections that have started.
// Sections which have been altered by a change file entry have their ≪changed_section≫ flag turned on during the first phase.
boolean change_exists;	// has any section changed?
// 1.1.2†1.1.4: Global variables (2/24)
xref_info xmem[max_refs];	// contains cross-reference information
xref_pointer xmem_end = xmem + max_refs - 1;
xref_pointer xref_ptr;				// the largest occupied position in ≪xmem≫
sixteen_bits xref_switch, section_xref_switch;	// either zero or ≪def_flag≫
// 1.1.4†1.1.10: Global variables (3/24)
// The first position of ≪tok_mem≫ that is unoccupied by replacement text is called ≪tok_ptr≫, and the first unused location of ≪tok_start≫ is called ≪text_ptr≫.
// Thus, we usually have ≪*text_ptr ≡ tok_ptr≫.
token tok_mem[max_toks];		// tokens
token_pointer tok_mem_end = tok_mem + max_toks - 1;	// end of ≪tok_mem≫
token_pointer tok_start[max_texts];	// directory into ≪tok_mem≫
token_pointer tok_ptr;			// first unused position in ≪tok_mem≫
text_pointer text_ptr;			// first unused position in ≪tok_start≫
text_pointer tok_start_end = tok_start + max_texts - 1;	// end of ≪tok_start≫
token_pointer max_tok_ptr;		// largest value of ≪tok_ptr≫
text_pointer max_text_ptr;		// largest value of ≪text_ptr≫
// 1.1.10†1.2.3: Global variables (4/24)
// Control codes are converted to ‹CWEAVE›'s internal representation by means of the table ≪ccode≫.
eight_bits ccode[0x100];	// meaning of a char following ‹@›
// 1.2.3†1.3.1: Global variables (5/24)
// As stated above, ‹CWEAVE›'s most interesting lexical scanning routine is the ≪get_next≫ function that inputs the next token of ‹C99› input.
// However, ≪get_next≫ is not especially complicated.

// The result of ≪get_next≫ is either a ≪char≫ code for some special character, or it is a special code representing a pair of characters (e.g., ‛‹!=›’),
// or it is the numeric value computed by the ≪ccode≫ table, or it is one of the following special codes:
// ∙	≪identifier≫:	In this case the global variables ≪id_first≫ and ≪id_loc≫ will have been set to the beginning and ending-plus-one locations in the buffer,
//			as required by the ≪id_lookup≫ routine.
// ∙	≪string≫:	The string will have been copied into the array ≪section_text≫;
//			≪id_first≫ and ≪id_loc≫ are set as above (now they are pointers into ≪section_text≫).
// ∙	≪constant≫:	The constant is copied into ≪section_text≫, with slight modifications; ≪id_first≫ and ≪id_loc≫ are set.

// Furthermore, some of the control codes cause ≪get_next≫ to take additional actions:
// ∙	≪xref_roman≫, ≪xref_wildcard≫, ≪xref_typewriter≫, ≪TeX_string≫, ≪verbatim≫:
//	The values of ≪id_first≫ and ≪id_loc≫ will have been set to the beginning and ending-plus-one locations in the buffer.
// ∙	≪section_name≫:
//	In this case the global variable ≪cur_section≫ will point to the ≪byte_start≫ entry for the section name that has just been scanned.
//	The value of ≪cur_section_char≫ will be ≪'('≫ if the section name was preceded by ‹@(› instead of ‹@<›.
// If ≪get_next≫ sees ‛‹@!›’ it sets ≪xref_switch≫ to ≪def_flag≫ and goes on to the next token.

#define constant	0x80	// ‹C99› constant
#define string		0x81	// ‹C99› string
#define identifier	0x82	// ‹C99› identifier or reserved word

name_pointer cur_section;	// name of section just scanned
char cur_section_char;		// the character just before that name
// 1.3.1†1.3.5: Global variables (6/24)
// Because preprocessor commands do not fit in with the rest of the syntax of ‹C99›, we have to deal with them separately.
// One solution is to enclose such commands between special markers.
// Thus, when a ‹#› is seen as the first character of a line, ≪get_next≫ returns a special code ≪left_preproc≫ and raises a flag ≪preprocessing≫.

// We can use the same internal code number for ≪left_preproc≫ as we do for ≪ord≫, since ≪get_next≫ changes ≪ord≫ into a string.
#define left_preproc ord	// begins a preprocessor command
#define right_preproc 0217	// ends a preprocessor command

boolean preprocessing = 0;	// are we scanning a preprocessor command?
// 1.3.5†1.3.7: Global variables (7/24)
// An additional complication is the freakish use of ‹<› and ‹>› to delimit a file name in lines that start with ‹#include›.
// We must treat this file name as a string.
boolean sharp_include_line = 0;	// are we scanning a ≪#include≫ line?
// 1.3.7†2.0.1: Global variables (8/24)
// We now have accumulated enough subroutines to make it possible to carry out ‹CWEAVE›'s first pass over the source file.
// If everything works right, both phase one and phase two of ‹CWEAVE› will assign the same numbers to sections, and these numbers will agree with what ‹CTANGLE› does.

// The global variable ≪next_control≫ often contains the most recent output of ≪get_next≫; in interesting cases,
// this will be the control code that ended a section or part of a section.
eight_bits next_control;	// control code waiting to be acting upon
// 2.0.1†2.0.11: Global variables (9/24)
// During the definition and ‹C99› parts of a section, cross-references are made for all identifiers except reserved words.
// However, the right identifier in a format definition is not referenced,
// and the left identifier is referenced only if it has been explicitly underlined (preceded by ‹@!›).
// The ‹TeX› code in comments is, of course, ignored, except for ‹C99› portions enclosed in ‹pb›;
// the text of a section name is skipped entirely, even if it contains ‹pb› constructions.

// The variables ≪lhs≫ and ≪rhs≫ point to the respective identifiers involved in a format definition.
name_pointer lhs, rhs;	// pointers to ≪byte_start≫ for format identifiers
name_pointer res_wd_end;	// pointer to the first nonreserved identifier
// 2.0.11†2.0.16: Global variables (10/24)
// After phase one has looked at everything, we want to check that each section name was both defined and used.
// The variable ≪cur_xref≫ will point to cross-references for the current section name of interest.
xref_pointer cur_xref;	// temporary cross-reference pointer
boolean an_output;	// did ≪file_flag≫ precede ≪cur_xref≫?
// 2.0.16†2.1.1: Global variables (11/24)
// The ‹TeX› output is supposed to appear in lines at most ≪line_length≫ characters long, so we place it into an output buffer.
// During the output process, ≪out_line≫ will hold the current line number of the line about to be output.
char out_buf[line_length + 1];	// assembled characters
char *out_ptr;	// last character in ≪out_buf≫
char *out_buf_end = out_buf + line_length;	// end of ≪out_buf≫
int out_line;	// number of next line to be output
// 2.1.1†3.0.2: Global variables (12/24)
// Here is a list of the category codes that scraps can have.
// (A few others, like ≪int_like≫, have already been defined; the ≪cat_name≫ array contains a complete list.)
#define exp		1	// denotes an expression, including perhaps a single identifier
#define unop		2	// denotes a unary operator
#define binop		3	// denotes a binary operator
#define ubinop		4	// denotes an operator that can be unary or binary, depending on context
#define cast		5	// denotes a cast
#define question	6	// denotes a question mark and possibly the expressions flanking it
#define lbrace		7	// denotes a left brace
#define rbrace		8	// denotes a right brace
#define decl_head	9	// denotes an incomplete declaration
#define comma		10	// denotes a comma
#define lpar		11	// denotes a left parenthesis or left bracket
#define rpar		12	// denotes a right parenthesis or right bracket
#define prelangle	13	// denotes ‛<’ before we know what it is
#define prerangle	14	// denotes ‛>’ before we know what it is
#define langle		15	// denotes ‛<’ when it's used as angle bracket in a template
#define colcol		18	// denotes ‛::’
#define base		19	// denotes a colon that introduces a base specifier
#define decl		20	// denotes a complete declaration
#define struct_head	21	// denotes the beginning of a structure specifier
#define stmt		23	// denotes a complete statement
#define function	24	// denotes a complete function
#define fn_decl		25	// denotes a function declarator
#define semi		27	// denotes a semicolon
#define colon		28	// denotes a colon
#define tag		29	// denotes a statement label
#define if_head		30	// denotes the beginning of a compound conditional
#define else_head	31	// denotes a prefix for a compound statement
#define if_clause	32	// pending ‹if› together with a condition
#define lproc		35	// begins a preprocessor command
#define rproc		36	// ends a preprocessor command
#define insert		37	// a scrap that gets combined with its neighbor
#define section_scrap	38	// section name
#define dead		39	// scrap that won't combine
#define ftemplate	59	// «make_pair»
#define new_exp		60	// «new» and a following type identifier
#define begin_arg	61	// ‹@[›
#define end_arg		62	// ‹@]›

char cat_name[0x100][12];
eight_bits cat_index;
// 3.0.2†3.1.2: Global variables (13/24)
#define trans trans_plus.Trans	// translation texts of scraps
scrap scrap_info[max_scraps];	// memory array for scraps
scrap_pointer scrap_info_end = scrap_info + max_scraps - 1;	// end of ≪scrap_info≫
scrap_pointer pp;		// current position for reducing productions
scrap_pointer scrap_base;	// beginning of the current scrap sequence
scrap_pointer scrap_ptr;	// ending of the current scrap sequence
scrap_pointer lo_ptr;		// last scrap that has been examined
scrap_pointer hi_ptr;		// first scrap that has not been examined
scrap_pointer max_scr_ptr;	// largest value assumed by ≪scrap_ptr≫
// 3.1.2†3.1.6: Global variables (14/24)
// The production rules listed above are embedded directly into ‹CWEAVE›,
// since it is easier to do this than to write an interpretive system that would handle production systems in general.
// Several macros are defined here so that the program for each production is fairly short.

// All of our productions conform to the general notion that some ≪k≫ consecutive scraps starting at some position ≪j≫
// are to be replaced by a single scrap of some category ≪c≫ whose translation is composed from the translations of the disappearing scraps.
// After this production has been applied, the production pointer ≪pp≫ should change by an amount ≪d≫.
// Such a production can be represented by the quadruple ≪(j, k, c, d)≫.
// For example, the production ‛≪exp comma exp≫ $→$ ≪exp≫’ would be represented by ‛≪(pp, 3, exp, -2)≫’;
// in this case the pointer ≪pp≫ should decrease by 2 after the production has been applied,
// because some productions with ≪exp≫ in their second or third positions might now match,
// but no productions have ≪exp≫ in the fourth position of their left-hand sides.
// Note that the value of ≪d≫ is determined by the whole collection of productions, not by an individual one.
// The determination of ≪d≫ has been done by hand in each case,
// based on the full set of productions but not on the grammar of ‹C99› or on the rules for constructing the initial scraps.

// We also attach a serial number to each production, so that additional information is available when debugging.
// For example, the program below contains the statement ‛≪reduce(pp, 3, exp, -2, 4)≫’ when it implements the production just mentioned.

// Before calling ≪reduce≫, the program should have appended the tokens of the new translation to the ≪tok_mem≫ array.
// We commonly want to append copies of several existing translations, and macros are defined to simplify these common cases.
// For example, ≪app2(pp)≫ will append the translations of two consecutive scraps, ≪pp→trans≫ and ≪(pp + 1)→trans≫, to the current token list.
// If the entire new translation is formed in this way, we write ‛≪squash(j, k, c, d, n)≫’ instead of ‛≪reduce(j, k, c, d, n)≫’.
// For example, ‛≪squash(pp, 3, exp, -2, 3)≫’ is an abbreviation for `≪app3(pp); reduce(pp, 3, exp, -2, 3)≫'.

// A couple more words of explanation:
// Both ≪big_app≫ and ≪app≫ append a token (while ≪big_app1≫ to ≪big_app4≫ append the specified number of scrap translations) to the current token list.
// The difference between ≪big_app≫ and ≪app≫ is simply that ≪big_app≫
// checks whether there can be a conflict between math and non-math tokens, and intercalates a ‛‹$›’ token if necessary.
// When in doubt what to use, use ≪big_app≫.

// The ≪mathness≫ is an attribute of scraps that says whether they are to be printed in a math mode context or not.
// It is separate from the ‟part of speech” (the ≪cat≫) because to make each ≪cat≫ have a fixed ≪mathness≫ (as in the original ‹WEAVE›)
// would multiply the number of necessary production rules.

// The low two bits (i.e. ≪mathness%4≫) control the left boundary.
// (We need two bits because we allow cases ≪yes_math≫, ≪no_math≫ and ≪maybe_math≫, which can go either way.)
// The next two bits (i.e. ≪mathness/4≫) control the right boundary.
// If we combine two scraps and the right boundary of the first has a different mathness from the left boundary of the second, we insert a ‹$› in between.
// Similarly, if at printing time some irreducible scrap has a ≪yes_math≫ boundary the scrap gets preceded or followed by a ‹$›.
// The left boundary is ≪maybe_math≫ if and only if the right boundary is.

// The code below is an exact translation of the production rules into ‹C99›, using such macros,
// and the reader should have no difficulty understanding the format by comparing the code with the symbolic productions as they were listed earlier.
#define no_math 2	// should be in horizontal mode
#define yes_math 1	// should be in math mode
#define maybe_math 0	// works in either horizontal or math mode
#define big_app2(a) (big_app1(a), big_app1(a + 1))
#define big_app3(a) (big_app2(a), big_app1(a + 2))
#define big_app4(a) (big_app3(a), big_app1(a + 3))
#define app(a) *tok_ptr↑ = a
#define app1(a) *tok_ptr↑ = tok_flag + (int)((a)→trans - tok_start)

int cur_mathness, init_mathness;
// 3.1.6†3.1.66: Global variables (15/24)
// If ‹CWEAVE› is being run in debugging mode, the production numbers and current stack categories will be printed out when ≪tracing≫ is set to 2;
// a sequence of two or more irreducible scraps will be printed out when ≪tracing≫ is set to 1.
int tracing;	// can be used to show parsing details
// 3.1.66†3.3.3: Global variables (16/24)
#define cur_end cur_state.end_field	// current ending location in ≪tok_mem≫
#define cur_tok cur_state.tok_field	// location of next output token in ≪tok_mem≫
#define cur_mode cur_state.mode_field	// current mode of interpretation
#define init_stack() (stack_ptr = stack, cur_mode = outer)	// initialize the stack
output_state cur_state;	// ≪cur_end≫, ≪cur_tok≫, ≪cur_mode≫
output_state stack[stack_size];	// info for non-current levels
stack_pointer stack_ptr;	// first unused location in the output state stack
stack_pointer stack_end = stack + stack_size - 1;	// end of ≪stack≫
stack_pointer max_stack_ptr;	// largest value assumed by ≪stack_ptr≫
// 3.3.3†3.3.7: Global variables (17/24)
// The ≪get_output≫ function returns the next byte of output that is not a reference to a token list.
// It returns the values ≪identifier≫ or ≪res_word≫ or ≪section_code≫ if the next token is to be an identifier (typeset in italics),
// a reserved word (typeset in boldface), or a section name (typeset by a complex routine that might generate additional levels of output).
// In these cases ≪cur_name≫ points to the identifier or section name in question.
name_pointer cur_name;
// 3.3.7†4.3: Global variables (18/24)
// The output file will contain the control sequence ‹\Y› between non-null sections of a section,
// e.g., between the ‹TeX› and definition parts if both are nonempty.
// This puts a little white space between the parts when they are printed.
// However, we don't want ‹\Y› to occur between two definitions within a single section.
// The variables ≪out_line≫ or ≪out_ptr≫ will change if a section is non-null,
// so the following macros ‛≪save_position()≫’ and ‛≪emit_space_if_needed()≫’ are able to handle the situation:
#define save_position() (save_line = out_line, save_place = out_ptr)
inline void emit_space_if_needed(void) {
   if (save_line ≠ out_line ∨ save_place ≠ out_ptr) out_str("\\Y");
   space_checked = 1	// ⁅001⁆
}

int save_line;			// former value of ≪out_line≫
char *save_place;		// former value of ≪out_ptr≫
int sec_depth;			// the integer, if any, following ‹@*›
boolean space_checked;		// have we done ≪emit_space_if_needed()≫?
boolean format_visible;		// should the next format declaration be output?
boolean doing_format = 0;	// are we outputting a format declaration?
boolean group_found = 0;	// has a starred section occurred?
// 4.3†4.12: Global variables (19/24)
// Finally, when the ‹TeX› and definition parts have been treated, we have ≪next_control ≥ begin_C≫.
// We will make the global variable ≪this_section≫ point to the current section name, if it has a name.
name_pointer this_section;	// the current section name, or zero
// 4.12†5.3: Global variables (20/24)
// Just before the index comes a list of all the changed sections, including the index section itself.
sixteen_bits k_section;	// runs through the sections
// 5.3†5.5: Global variables (21/24)
// A left-to-right radix sorting method is used, since this makes it easy to adjust the collating sequence
// and since the running time will be at worst proportional to the total length of all entries in the index.
// We put the identifiers into 102 different lists based on their first characters.
// (Uppercase letters are put into the same list as the corresponding lowercase letters, since we want to have ‛t<\{TeX} < «to»’.)
// The list for character ≪c≫ begins at location ≪bucket[c]≫ and continues through the ≪blink≫ array.
name_pointer bucket[0x100];
name_pointer next_name;	// successor of ≪cur_name≫ when sorting
name_pointer blink[max_names];	// links in the buckets
// 5.5†5.9: Global variables (22/24)
#define depth cat	// reclaims memory that is no longer needed for parsing
#define head trans_plus.Head	// ditto
// #format sort_pointer int
#define sort_pointer scrap_pointer	// ditto
#define sort_ptr scrap_ptr	// ditto
#define max_sorts max_scraps	// ditto

eight_bits cur_depth;	// depth of current buckets
char *cur_byte;	// index into ≪byte_mem≫
sixteen_bits cur_val;	// current cross-reference number
sort_pointer max_sort_ptr;	// largest value of ≪sort_ptr≫
// 5.9†5.11: Global variables (23/24)
// The desired alphabetic order is specified by the ≪collate≫ array; namely, ≪collate≫[0] < ≪collate≫[1] < ⋯ < ≪collate≫[100].
eight_bits collate[102 + 128];	// collation order ⁅002⁆
// 5.11†5.20: Global variables (24/24)
// List inversion is best thought of as popping elements off one stack and pushing them onto another.
// In this case ≪cur_xref≫ will be the head of the stack that we push things onto.
xref_pointer next_xref, this_xref;	// pointer variables for rearranging a list
// 5.20†

// †1.0.2: Predeclaration of procedures (1/19)
// Editor's Note:
// ∙	These routines were originally declared here (with legacy declarations), since pre-C99 compilers did not standardize the header file.
// extern size_t strlen(const char *S);					// the length of string ≪S≫.
// extern int strcmp(const char *S0, const char *S1);			// compare strings ≪S0≫ and ≪S1≫ lexicographically.
// extern char *strcpy(char *AdS, char *DeS);				// copy string ≪DeS≫ to ≪AdS≫ and return the ≪AdS≫.
// extern int strncmp(const char *S0, const char *S1, size_t N);	// compare up to ≪N≫ string characters of ≪S0≫ and ≪S1≫.
// extern char *strncpy(char *AdS, char *DeS, size_t N);		// copy up to ≪N≫ string characters of ≪DeS≫ to ≪AdS≫ and return ≪AdS≫.
#include <string.h>
// 1.0.2†1.2.6: Predeclaration of procedures (2/19)
// The ≪skip_limbo≫ routine is used on the first pass to skip through portions of the input that are not in any sections, i.e., that precede the first section.
// After this procedure has been called, the value of ≪input_has_ended≫ will tell whether or not a section has actually been found.

// There's a complication that we will postpone until later: If the ‹@s› operation appears in limbo, we want to use it to adjust the default interpretation of identifiers.
void skip_limbo(void);
// 1.2.6†1.3.3: Predeclaration of procedures (3/19)
// As one might expect, ≪get_next≫ consists mostly of a big switch that branches to the various special cases that can arise.
// ‹C99› allows underscores to appear in identifiers, and some ‹C99› compilers even allow the dollar sign.
#define isxalpha(c) ((c) ≡ '_' ∨ (c) ≡ '$')	// non-alpha characters allowed in identifier ⁅003⁆
#define ishigh(c) ((eight_bits)(c) > 0x7f)
eight_bits get_next(void);
// 1.3.3†1.3.19: Predeclaration of procedures (4/19)
// This function skips over a restricted context at relatively high speed.
void skip_restricted(void);
// 1.3.19†2.0.2: Predeclaration of procedures (5/19)
// The overall processing strategy in phase one has the following straightforward outline.
void phase_one(void);
// 2.0.2†2.0.5: Predeclaration of procedures (6/19)
// The ≪C_xref≫ subroutine stores references to identifiers in ‹C99› text material beginning with the current value of ≪next_control≫
// and continuing until ≪next_control≫ is ‛‹{›’ or ‛‹|›’, or until the next ‟milestone” is passed (i.e., ≪next_control ≥ format_code≫).
// If ≪next_control ≥ format_code≫ when ≪C_xref≫ is called, nothing will happen;
// but if ≪next_control ≡ '|'≫ upon entry, the procedure assumes that this is the ‛‹|›’ preceding ‹C99› text that is to be processed.

// The parameter ≪spec_ctrl≫ is used to change this behavior.
// In most cases ≪C_xref≫ is called with ≪spec_ctrl ≡ ignore≫, which triggers the default processing described above.
// If ≪spec_ctrl ≡ section_name≫, section names will be gobbled. This is used when ‹C99› text in the ‹TeX› part or inside comments is parsed:
// It allows for section names to appear in ‹pb›, but these strings will not be entered into the cross reference lists since they are not definitions of section names.

// The program uses the fact that our internal code numbers satisfy the relations
// ≪xref_roman ≡ identifier + roman≫ and ≪xref_wildcard ≡ identifier + wildcard≫ and ≪xref_typewriter ≡ identifier + typewriter≫, as well as ≪normal ≡ 0≫.
void C_xref(eight_bits spec_ctrl);
// 2.0.5†2.0.7: Predeclaration of procedures (7/19)
// The ≪outer_xref≫ subroutine is like ≪C_xref≫ except that it begins with ≪next_control ≠ '≫'≪ and ends with ≫next_control ≥ format_code|.
// Thus, it handles ‹C99› text with embedded comments.
void outer_xref(void);
// 2.0.7†2.0.17: Predeclaration of procedures (8/19)
// The following recursive procedure walks through the tree of section names and prints out anomalies. ⁅004⁆
void section_check(name_pointer p);
// 2.0.17†2.1.7: Predeclaration of procedures (9/19)
// A long line is broken at a blank space or just before a backslash that isn't preceded by another backslash.
// In the latter case, a ≪'%'≫ is output at the break.
void break_out(void);
// 2.1.7†2.2.4: Predeclaration of procedures (10/19)
// The ≪copy_comment≫ function issues a warning if more braces are opened than closed,
// and in the case of a more serious error it supplies enough braces to keep ‹TeX› from complaining about unbalanced braces.
// Instead of copying the ‹TeX› material into the output buffer, this function copies it into the token memory (in phase two only).
// The abbreviation ≪app_tok(t)≫ is used to append token ≪t≫ to the current token list,
// and it also makes sure that it is possible to append at least one further token without overflow.
#define app_tok(c) {
   if (tok_ptr + 2 > tok_mem_end) overflow("token");
   *tok_ptr↑ = c;
}

int copy_comment(boolean is_long_comment, int bal);
// 2.2.4†3.1.12: Predeclaration of procedures (11/19)
// We cannot use ≪new_xref≫ to underline a cross-reference at this point because this would just make a new cross-reference at the end of the list.
// We actually have to search through the list for the existing cross-reference.
void underline_xref(name_pointer p);
// 3.1.12†3.2.8: Predeclaration of procedures (12/19)
// The function ≪app_cur_id≫ appends the current identifier to the token list; it also builds a new scrap if ≪scrapping ≡ 1≫.
void app_cur_id(boolean scrapping);
// 3.2.8†3.3.10: Predeclaration of procedures (13/19)
// Here is ‹CWEAVE›'s major output handler.
void make_output(void);
// 3.3.10†4.1: Predeclaration of procedures (14/19)
// We have assembled enough pieces of the puzzle in order to be ready to specify the processing in ‹CWEAVE›'s main pass over the source file.
// Phase two is analogous to phase one, except that more work is involved
// because we must actually output the ‹TeX› material instead of merely looking at the ‹CWEB› specifications.
void phase_two(void);
// 4.1†4.8: Predeclaration of procedures (15/19)
// The ≪finish_C≫ procedure outputs the translation of the current scraps, preceded by the control sequence ‛‹\B›’ and followed by the control sequence ‛‹\par›’.
// It also restores the token and scrap memories to their initial empty state.

// A ≪force≫ token is appended to the current scraps before translation takes place,
// so that the translation will normally end with ‹\6› or ‹\7› (the ‹TeX› macros for ≪force≫ and ≪big_force≫).
// This ‹\6› or ‹\7› is replaced by the concluding ‹\par› or by ‹\Y\par›.
void finish_C(boolean visible);
// 4.8†4.17: Predeclaration of procedures (16/19)
// The ≪footnote≫ procedure gives cross-reference information about multiply defined section names (if the ≪flag≫ parameter is ≪def_flag≫),
// or about references to a section name (if ≪flag ≡ cite_flag≫), or to its uses (if ≪flag ≡ 0≫).
// It assumes that ≪cur_xref≫ points to the first cross-reference entry of interest, and it leaves ≪cur_xref≫ pointing to the first element not printed.
// Typical outputs:
//	‛‹\A101.›’;
//	‛‹\Us 370\ET1009.›’;
//	‛‹\As 8, 27\*\ETs64.›’.

// Note that the output of ‹CWEAVE› is not English-specific; users may supply new definitions for the macros ‹\A›, ‹\As›, etc.
void footnote(sixteen_bits flag);
// 4.17†5.1: Predeclaration of procedures (17/19)
// We are nearly finished! ‹CWEAVE›'s only remaining task is to write out the index, after sorting the identifiers and index entries.

// If the user has set the ≪no_xref≫ flag (the ‹-x› option on the command line), just finish off the page, omitting the index, section name list, and table of contents.
void phase_three(void);
// 5.1†5.13: Predeclaration of procedures (18/19)
// Procedure ≪unbucket≫ goes through the buckets and adds nonempty lists to the stack, using the collating sequence specified in the ≪collate≫ array.
// The parameter to ≪unbucket≫ tells the current depth in the buckets.
// Any two sequences that agree in their first 0xff character positions are regarded as identical.
#define infinity 0xff	// ∞ (approximately)

void unbucket(eight_bits d);
// 5.13†5.22: Predeclaration of procedures (19/19)
// The following recursive procedure walks through the tree of section names and prints them. ⁅005⁆
void section_print(name_pointer p);
// 5.22†

// 1.0.1†1.0.3:
// ‹CWEAVE› has a fairly straightforward outline.
// It operates in three phases: First it inputs the source file and stores cross-reference data,
// then it inputs the source once again and produces the ‹TeX› output file, finally it sorts and outputs the index.

// Please read the documentation for ‹common›, the set of routines common to ‹CTANGLE› and ‹CWEAVE›, before proceeding further.
// ac: argument count; av: argument values.
int main(int ac, char **av) {
   argc = ac, argv = av;
   program = cweave;
   make_xrefs = force_lines = make_pb = 1;	// controlled by command-line options
   common_init();
// †1.1.5: Set initial values (1/11)
// A section that is used for multi-file output (with the ‹@(› feature) has a special first cross-reference whose ≪num≫ field is ≪file_flag≫.
#define file_flag (3*cite_flag)
#define def_flag (2*cite_flag)
#define cite_flag 0x2800	// must be strictly larger than ≪max_sections≫
#define xref equiv_or_xref
   xref_ptr = xmem, name_dir→xref = (char *)xmem, xref_switch = 0, section_xref_switch = 0;
   xmem→num = 0;	// sentinel value
// 1.1.5†1.1.11: Set initial values (2/11)
   tok_ptr = tok_mem + 1, text_ptr = tok_start + 1, tok_start[0] = tok_mem + 1,
   tok_start[1] = tok_mem + 1,
   max_tok_ptr = tok_mem + 1, max_text_ptr = tok_start + 1;
// 1.1.11†1.2.4: Set initial values (3/11)
   for (int c = 0; c < 0x100; c↑) ccode[c] = 0;
   ccode[' '] = ccode['\t'] = ccode['\n'] = ccode['|'] = ccode['\r'] = ccode['\f']  = ccode['*'] = new_section;
   ccode['@'] = '@';	// ‛quoted’ at sign
   ccode['='] = verbatim;
   ccode['d'] = ccode['D'] = definition;
   ccode['f'] = ccode['F'] = ccode['s'] = ccode['S'] = format_code;
   ccode['c'] = ccode['C'] = ccode['p'] = ccode['P'] = begin_C;
   ccode['t'] = ccode['T'] = TeX_string;
   ccode['l'] = ccode['L'] = translit_code;
   ccode['q'] = ccode['Q'] = noop;
   ccode['h'] = ccode['H'] = output_defs_code;
   ccode['&'] = join, ccode['<'] = ccode['('] = section_name;
   ccode['!'] = underline, ccode['^'] = xref_roman;
   ccode[':'] = xref_wildcard, ccode['.'] = xref_typewriter, ccode[','] = thin_space;
   ccode['|'] = math_break, ccode['/'] = line_break, ccode['#'] = big_line_break;
   ccode['+'] = no_line_break, ccode[';'] = pseudo_semi;
   ccode['['] = macro_arg_open, ccode[']'] = macro_arg_close;
   ccode['\''] = ord;
// †1.2.5: Special control codes for debugging
// Users can write ‹@2›, ‹@1›, and ‹@0› to turn tracing fully on, partly on, and off, respectively.
   ccode['0'] = ccode['1'] = ccode['2'] = trace;
// 1.2.5†
// 1.2.4†1.3.16: Set initial values (4/11)
// Section names are placed into the ≪section_text≫ array with consecutive spaces, tabs, and carriage-returns replaced by single spaces.
// There will be no spaces at the beginning or the end. (We set ≪section_text[0] = ' '≫ to facilitate this,
// since the ≪section_lookup≫ routine uses ≪section_text[1]≫ as the first character of the name.)
   section_text[0] = ' ';
// 1.3.16†2.1.4: Set initial values (5/11)
// In particular, the ≪finish_line≫ procedure is called near the very beginning of phase two.
// We initialize the output variables in a slightly tricky way so that the first line of the output file will be ‛‹\input cwebmac›’.
   out_ptr = out_buf + 1, out_line = 1, active_file = tex_file,
   *out_ptr = 'c', tex_printf("\\input cwebma");
// 2.1.4†2.1.6: Set initial values (6/11)
// The ≪break_out≫ routine is called just before the output buffer is about to overflow.
// To make this routine a little faster, we initialize position 0 of the output buffer to ‛‹\›’; this character isn't really output.
   out_buf[0] = '\\';
// 2.1.6†3.0.3: Set initial values (7/11)
   for (cat_index = 0; cat_index < 0xff; cat_index↑) strcpy(cat_name[cat_index], "UNKNOWN");	// ⁅006⁆
   strcpy(cat_name[exp], "exp");
   strcpy(cat_name[unop], "unop");
   strcpy(cat_name[binop], "binop");
   strcpy(cat_name[ubinop], "ubinop");
   strcpy(cat_name[cast], "cast");
   strcpy(cat_name[question], "?");
   strcpy(cat_name[lbrace], "{"/*}*/);
   strcpy(cat_name[rbrace], /*{*/"}");
   strcpy(cat_name[decl_head], "decl_head");
   strcpy(cat_name[comma], ", ");
   strcpy(cat_name[lpar], "(");
   strcpy(cat_name[rpar], ")");
   strcpy(cat_name[prelangle], "<");
   strcpy(cat_name[prerangle], ">");
   strcpy(cat_name[langle], "\\<");
   strcpy(cat_name[colcol], "::");
   strcpy(cat_name[base], "\\:");
   strcpy(cat_name[decl], "decl");
   strcpy(cat_name[struct_head], "struct_head");
   strcpy(cat_name[alfop], "alfop");
   strcpy(cat_name[stmt], "stmt");
   strcpy(cat_name[function], "function");
   strcpy(cat_name[fn_decl], "fn_decl");
   strcpy(cat_name[else_like], "else_like");
   strcpy(cat_name[semi], ";");
   strcpy(cat_name[colon], ":");
   strcpy(cat_name[tag], "tag");
   strcpy(cat_name[if_head], "if_head");
   strcpy(cat_name[else_head], "else_head");
   strcpy(cat_name[if_clause], "if()");
   strcpy(cat_name[lproc], "#{"/*}*/);
   strcpy(cat_name[rproc], /*{*/"#}");
   strcpy(cat_name[insert], "insert");
   strcpy(cat_name[section_scrap], "section");
   strcpy(cat_name[dead], "@d");
   strcpy(cat_name[public_like], "public");
   strcpy(cat_name[operator_like], "operator");
   strcpy(cat_name[new_like], "new");
   strcpy(cat_name[catch_like], "catch");
   strcpy(cat_name[for_like], "for");
   strcpy(cat_name[do_like], "do");
   strcpy(cat_name[if_like], "if");
   strcpy(cat_name[delete_like], "delete");
   strcpy(cat_name[raw_ubin], "ubinop?");
   strcpy(cat_name[const_like], "const");
   strcpy(cat_name[raw_int], "raw");
   strcpy(cat_name[int_like], "int");
   strcpy(cat_name[case_like], "case");
   strcpy(cat_name[sizeof_like], "sizeof");
   strcpy(cat_name[struct_like], "struct");
   strcpy(cat_name[typedef_like], "typedef");
   strcpy(cat_name[define_like], "define");
   strcpy(cat_name[template_like], "template");
   strcpy(cat_name[ftemplate], "ftemplate");
   strcpy(cat_name[new_exp], "new_exp");
   strcpy(cat_name[begin_arg], "@["/*]*/);
   strcpy(cat_name[end_arg], /*[*/"@]");
   strcpy(cat_name[0], "zero");
// 3.0.3†3.1.3: Set initial values (8/11)
   scrap_base = scrap_info + 1, max_scr_ptr = scrap_ptr = scrap_info;
// 3.1.3†3.3.4: Set initial values (9/11)
   max_stack_ptr = stack;
// 3.3.4†5.10: Set initial values (10/11)
   max_sort_ptr = scrap_info;
// 5.10†5.12: Set initial values (11/11)
// We use the order null < ‹.› < other characters < ‹_› < ‹A› = ‹a› < ⋯ < ‹Z› = ‹z› < ‹0› < ⋯ < ‹9›.
// Warning: The collation mapping needs to be changed if ASCII code is not being used. ⁅007⁆⁅008⁆

// We initialize ≪collate≫ by copying a few characters at a time, because some ‹C99› compilers choke on long strings.
   collate[0] = 0;
   strcpy(collate + 1, " \1\2\3\4\5\6\7\10\11\12\13\14\15\16\17");
// 16 characters + 1 = 17
   strcpy(collate + 17, "\20\21\22\23\24\25\26\27\30\31\32\33\34\35\36\37");
// 16 characters + 17 = 33
   strcpy(collate + 33, "!\42#$%&'()*+,-./:;<=>?@[\\]^`{|}~_");
// 32 characters + 33 = 65
   strcpy(collate + 65, "abcdefghijklmnopqrstuvwxyz0123456789");
// (26 + 10) characters + 65 = 101
   strcpy(collate + 101, "\200\201\202\203\204\205\206\207\210\211\212\213\214\215\216\217");
// 16 characters + 101 = 117
   strcpy(collate + 117, "\220\221\222\223\224\225\226\227\230\231\232\233\234\235\236\237");
// 16 characters + 117 = 133
   strcpy(collate + 133, "\240\241\242\243\244\245\246\247\250\251\252\253\254\255\256\257");
// 16 characters + 133 = 149
   strcpy(collate + 149, "\260\261\262\263\264\265\266\267\270\271\272\273\274\275\276\277");
// 16 characters + 149 = 165
   strcpy(collate + 165, "\300\301\302\303\304\305\306\307\310\311\312\313\314\315\316\317");
// 16 characters + 165 = 181
   strcpy(collate + 181, "\320\321\322\323\324\325\326\327\330\331\332\333\334\335\336\337");
// 16 characters + 181 = 197
   strcpy(collate + 197, "\340\341\342\343\344\345\346\347\350\351\352\353\354\355\356\357");
// 16 characters + 197 = 213
   strcpy(collate + 213, "\360\361\362\363\364\365\366\367\370\371\372\373\374\375\376\377");
// 16 characters + 213 = 229
// 5.12†
   if (show_banner) printf(banner);	// print a ‟banner line”
// †1.1.13: Store all the reserved words
// We have to get ‹C99›'s reserved words into the hash table, and the simplest way to do this is to insert them every time ‹CWEAVE› is run.
// Fortunately there are relatively few reserved words.
// (Some of these are not strictly ‟reserved,” but are defined in header files of the ISO Standard ‹C99› Library.) ⁅009⁆
   id_lookup("and", NULL, alfop);
   id_lookup("and_eq", NULL, alfop);
   id_lookup("asm", NULL, sizeof_like);
   id_lookup("auto", NULL, int_like);
   id_lookup("bitand", NULL, alfop);
   id_lookup("bitor", NULL, alfop);
   id_lookup("bool", NULL, raw_int);
   id_lookup("break", NULL, case_like);
   id_lookup("case", NULL, case_like);
   id_lookup("catch", NULL, catch_like);
   id_lookup("char", NULL, raw_int);
   id_lookup("class", NULL, struct_like);
   id_lookup("clock_t", NULL, raw_int);
   id_lookup("compl", NULL, alfop);
   id_lookup("const", NULL, const_like);
   id_lookup("const_cast", NULL, raw_int);
   id_lookup("continue", NULL, case_like);
   id_lookup("default", NULL, case_like);
   id_lookup("define", NULL, define_like);
   id_lookup("defined", NULL, sizeof_like);
   id_lookup("delete", NULL, delete_like);
   id_lookup("div_t", NULL, raw_int);
   id_lookup("do", NULL, do_like);
   id_lookup("double", NULL, raw_int);
   id_lookup("dynamic_cast", NULL, raw_int);
   id_lookup("elif", NULL, if_like);
   id_lookup("else", NULL, else_like);
   id_lookup("endif", NULL, if_like);
   id_lookup("enum", NULL, struct_like);
   id_lookup("error", NULL, if_like);
   id_lookup("explicit", NULL, int_like);
   id_lookup("export", NULL, int_like);
   id_lookup("extern", NULL, int_like);
   id_lookup("FILE", NULL, raw_int);
   id_lookup("float", NULL, raw_int);
   id_lookup("for", NULL, for_like);
   id_lookup("fpos_t", NULL, raw_int);
   id_lookup("friend", NULL, int_like);
   id_lookup("goto", NULL, case_like);
   id_lookup("if", NULL, if_like);
   id_lookup("ifdef", NULL, if_like);
   id_lookup("ifndef", NULL, if_like);
   id_lookup("include", NULL, if_like);
   id_lookup("inline", NULL, int_like);
   id_lookup("int", NULL, raw_int);
   id_lookup("jmp_buf", NULL, raw_int);
   id_lookup("ldiv_t", NULL, raw_int);
   id_lookup("line", NULL, if_like);
   id_lookup("long", NULL, raw_int);
   id_lookup("mutable", NULL, int_like);
   id_lookup("namespace", NULL, struct_like);
   id_lookup("new", NULL, new_like);
   id_lookup("not", NULL, alfop);
   id_lookup("not_eq", NULL, alfop);
   id_lookup("NULL", NULL, custom);
   id_lookup("offsetof", NULL, raw_int);
   id_lookup("operator", NULL, operator_like);
   id_lookup("or", NULL, alfop);
   id_lookup("or_eq", NULL, alfop);
   id_lookup("pragma", NULL, if_like);
   id_lookup("private", NULL, public_like);
   id_lookup("protected", NULL, public_like);
   id_lookup("ptrdiff_t", NULL, raw_int);
   id_lookup("public", NULL, public_like);
   id_lookup("register", NULL, int_like);
   id_lookup("reinterpret_cast", NULL, raw_int);
   id_lookup("return", NULL, case_like);
   id_lookup("short", NULL, raw_int);
   id_lookup("sig_atomic_t", NULL, raw_int);
   id_lookup("signed", NULL, raw_int);
   id_lookup("size_t", NULL, raw_int);
   id_lookup("sizeof", NULL, sizeof_like);
   id_lookup("static", NULL, int_like);
   id_lookup("static_cast", NULL, raw_int);
   id_lookup("struct", NULL, struct_like);
   id_lookup("switch", NULL, for_like);
   id_lookup("template", NULL, template_like);
   id_lookup("this", NULL, custom);
   id_lookup("throw", NULL, case_like);
   id_lookup("time_t", NULL, raw_int);
   id_lookup("try", NULL, else_like);
   id_lookup("typedef", NULL, typedef_like);
   id_lookup("typeid", NULL, raw_int);
   id_lookup("typename", NULL, struct_like);
   id_lookup("undef", NULL, if_like);
   id_lookup("union", NULL, struct_like);
   id_lookup("unsigned", NULL, raw_int);
   id_lookup("using", NULL, int_like);
   id_lookup("va_dcl", NULL, decl);	// Berkeley's variable-arg-list convention
   id_lookup("va_list", NULL, raw_int);	// ditto
   id_lookup("virtual", NULL, int_like);
   id_lookup("void", NULL, raw_int);
   id_lookup("volatile", NULL, const_like);
   id_lookup("wchar_t", NULL, raw_int);
   id_lookup("while", NULL, for_like);
   id_lookup("xor", NULL, alfop);
   id_lookup("xor_eq", NULL, alfop);
   res_wd_end = name_ptr;
   id_lookup("TeX", NULL, custom);
   id_lookup("make_pair", NULL, func_template);
// 1.1.13†
   phase_one();	// read all the user's text and store the cross-references
   phase_two();	// read all the text again and translate it to ‹TeX› form
   phase_three();	// output the cross-reference index
   return wrap_up();	// and exit gracefully
}

// 1.0.3†1.0.4:
// The following parameters were sufficient in the original ‹WEAVE› to handle ‹TeX›, so they should be sufficient for most applications of ‹CWEAVE›.
// If you change ≪max_bytes≫, ≪max_names≫, ≪hash_size≫, or ≪buf_size≫ you have to change them also in the file ≪"common.w"≫.
#define max_bytes	90000	// the number of bytes in identifiers, index entries, and section names
#define max_names	4000	// number of identifiers, strings, section names; must be less than 0x2800; used in ≪"common.w"≫
#define max_sections	2000	// greater than the total number of sections
#define hash_size	353	// should be prime
#define buf_size	100	// maximum length of input line, plus one
#define longest_name	10000	// section names and strings shouldn't be longer than this
#define long_buf_size	(buf_size + longest_name)
#define line_length	80	// lines of ‹TeX› output have at most this many characters; should be less than 0x100
#define max_refs	20000	// number of cross-references; must be less than 0x10000
#define max_toks	20000	// number of symbols in ‹C99› texts being parsed; must be less than 0x10000
#define max_texts	4000	// number of phrases in ‹C99› texts being parsed; must be less than 0x2800
#define max_scraps	2000	// number of tokens in ‹C99› texts being parsed
#define stack_size	400	// number of simultaneous output levels

// 1.0.4†1.0.5:
// The next few sections contain stuff from the file ≪"common.w"≫ that must be included in both ≪"ctangle.w"≫ and ≪"cweave.w"≫.
// It appears in file ≪"common.h"≫, which needs to be updated when ≪"common.w"≫ changes.
#include "Common.h"
// 1.0.5†

// ‡1.1. Data Structures Exclusive to ≪_ CWEAVE _≫.
// †1.1.1:
// As explained in ‹common.w›, the field of a ≪name_info≫ structure
// that contains the ≪rlink≫ of a section name is used for a completely different purpose in the case of identifiers.
// It is then called the ≪ilk≫ of the identifier, and it is used to distinguish between various types of identifiers, as follows:
// ∙	≪normal≫ and ≪func_template≫ identifiers are part of the ‹C99› program that will  appear in italic type (or in typewriter type if all uppercase).
// ∙	≪custom≫ identifiers are part of the ‹C99› program that will be typeset in special ways.
// ∙	≪roman≫ identifiers are index entries that appear after ‹@^› in the ‹CWEB› file.
// ∙	≪wildcard≫ identifiers are index entries that appear after ‹@:› in the ‹CWEB› file.
// ∙	≪typewriter≫ identifiers are index entries that appear after ‹@.› in the ‹CWEB› file.
// ∙	≪alfop≫, ⋯, ≪template_like≫ identifiers are ‹C99› or ‹C++› reserved words whose ≪ilk≫ explains how they are to be treated when ‹C99› code is being formatted.
#define ilk dummy.Ilk
#define normal		0	// ordinary identifiers have ≪normal≫ ilk
#define roman		1	// normal index entries have ≪roman≫ ilk
#define wildcard	2	// user-formatted index entries have ≪wildcard≫ ilk
#define typewriter	3	// ‛typewriter type’ entries have ≪typewriter≫ ilk
#define abnormal(a)	(a→ilk > typewriter)	// tells if a name is special
#define func_template	4	// identifiers that can be followed by optional template
#define custom		5	// identifiers with user-given control sequence
#define alfop		22	// alphabetic operators like «and» or «not_eq»
#define else_like	26	// «else»
#define public_like	40	// «public», «private», «protected»
#define operator_like	41	// «operator»
#define new_like	42	// «new»
#define catch_like	43	// «catch»
#define for_like	45	// «for», «switch», «while»
#define do_like		46	// «do»
#define if_like		47	// «if», «ifdef», «endif», «pragma», ⋯
#define delete_like	48	// «delete»
#define raw_ubin	49	// ‛‹&›’ or ‛‹*›’ when looking for «const» following
#define const_like	50	// «const», «volatile»
#define raw_int		51	// «int», «char», ⋯; also structure and class names
#define int_like	52	// same, when not followed by left parenthesis or ‹DC›
#define case_like	53	// «case», «return», «goto», «break», «continue»
#define sizeof_like	54	// «sizeof»
#define struct_like	55	// «struct», «union», «enum», «class»
#define typedef_like	56	// «typedef»
#define define_like	57	// «define»
#define template_like	58	// «template»

// 1.1.1†1.1.6:
// A new cross-reference for an identifier is formed by calling ≪new_xref≫,
// which discards duplicate entries and ignores non-underlined references to one-letter identifiers or ‹C99›'s reserved words.

// If the user has sent the ≪no_xref≫ flag (the ‹-x› option of the command line), it is unnecessary to keep track of cross-references for identifiers.
// If one were careful, one could probably make more changes around section 100 to avoid a lot of identifier looking up.
#define append_xref(c)	if (xref_ptr ≡ xmem_end) overflow("cross-reference"); else (↑xref_ptr)→num = c;
#define no_xref		(flags['x'] ≡ 0)
#define make_xrefs	flags['x']	// should cross references be output?
#define is_tiny(p)	((p + 1)→byte_start ≡ (p)→byte_start + 1)
#define unindexed(a)	(a < res_wd_end ∧ a→ilk ≥ custom)	// tells if uses of a name are to be indexed

void new_xref(name_pointer p) {
   if (no_xref ∨ (unindexed(p) ∨ is_tiny(p)) ∧ xref_switch ≡ 0) return;
   sixteen_bits m = section_count + xref_switch;	// new cross-reference value
   xref_switch = 0, xref_pointer q = (xref_pointer)p→xref;	// pointer to previous cross-reference
   if (q ≠ xmem) {
      sixteen_bits n = q→num;	// previous cross-reference value
      if (n ≡ m ∨ n ≡ m + def_flag) return;
      else if (m ≡ n + def_flag) { q→num = m; return; }
   }
   append_xref(m), xref_ptr→xlink = q, p→xref = (char *)xref_ptr;
}

// 1.1.6†1.1.7:
// The cross-reference lists for section names are slightly different.
// Suppose that a section name is defined in sections m_1, ⋯, m_k, cited in sections n_1, ⋯, n_l, and used in sections p_1, ⋯, p_j.
// Then its list will contain m_1 + ≪def_flag≫, ⋯, m_k + ≪def_flag≫, n_1 + ≪cite_flag≫, ⋯, n_l + ≪cite_flag≫, p_1, ⋯, p_j, in this order.

// Although this method of storage takes quadratic time with respect to the length of the list, under foreseeable uses of ‹CWEAVE› this inefficiency is insignificant.
void new_section_xref(name_pointer p) {
   xref_pointer q = (xref_pointer)p→xref, r = xmem;	// pointers to previous cross-references
   if (q > xmem) for (; q→num > section_xref_switch; r = q, q = q→xlink);
   if (r→num ≡ section_count + section_xref_switch) return;	// don't duplicate entries
   append_xref(section_count + section_xref_switch);
   xref_ptr→xlink = q, section_xref_switch = 0;
   if (r ≡ xmem) p→xref = (char *)xref_ptr; else r→xlink = xref_ptr;
}

// 1.1.7†1.1.8:
// The cross-reference list for a section name may also begin with ≪file_flag≫.
// Here's how that flag gets put in.
void set_file_flag(name_pointer p) {
   xref_pointer q = (xref_pointer)p→xref;
   if (q→num ≡ file_flag) return;
   append_xref(file_flag), xref_ptr→xlink = q, p→xref = (char *)xref_ptr;
}

// 1.1.8†1.1.12:
// Here are the three procedures needed to complete ≪id_lookup≫:
// p: points to the proposed match
// first: position of first character of string
// l: length of identifier
// t: desired ilk
int names_match(name_pointer p, char *first, int l, eight_bits t) {
   return length(p) = l ∧ (p→ilk = t ∨ t ≡ normal ∧ abnormal(p)) ∧ strncmp(first, p→byte_start, l) ≡ 0;
}

void init_p(name_pointer p, eight_bits t) { p→ilk = t, p→xref = (char *)xmem; }

void init_node(name_pointer p) { p→xref = (char *)xmem; }
// 1.1.12†

// ‡1.2. Lexical Scanning.
// †1.2.1:
// Let us now consider the subroutines that read the ‹CWEB› source file and break it into meaningful units.
// There are four such procedures:
//	One simply skips to the next ‛‹@ ›’ or ‛‹@*›’ that begins a section;
//	another passes over the ‹TeX› text at the beginning of a section;
//	the third passes over the ‹TeX› text in a ‹C99› comment;
//	and the last, which is the most interesting, gets the next token of a ‹C99› text.
// They all use the pointers ≪limit≫ and ≪loc≫ into the line of input currently being studied.

// 1.2.1†1.2.2:
// Control codes in ‹CWEB›, which begin with ‛‹@›’, are converted into a numeric code designed to simplify ‹CWEAVE›'s logic;
// for example, larger numbers are given to the control codes that denote more significant milestones, and the code of ≪new_section≫ should be the largest of all.
// Some of these numeric control codes take the place of ≪char≫ control codes that will not otherwise appear in the output of the scanning routines. ⁅010⁆
#define ignore			0x00	// control code of no interest to ‹CWEAVE›
#define verbatim		0x02	// takes the place of extended ASCII ‹‹char›2›
#define begin_short_comment	0x03	// ‹C++› short comment
#define begin_comment		'\t'	// tab marks will not appear
#define underline		'\n'	// this code will be intercepted without confusion
#define noop			0x7f	// takes the place of ASCII delete
#define xref_roman		0x83	// control code for ‛‹@^›’
#define xref_wildcard		0x84	// control code for ‛‹@:›’
#define xref_typewriter		0x85	// control code for ‛‹@.›’
#define TeX_string		0x86	// control code for ‛‹@t›’
// #format TeX_string TeX
#define ord			0x87	// control code for ‛‹@’›'
#define join			0x88	// control code for ‛‹@&›’
#define thin_space		0x89	// control code for ‛‹@,›’
#define math_break		0x8a	// control code for ‛‹@|›’
#define line_break		0x8b	// control code for ‛‹@/›’
#define big_line_break		0x8c	// control code for ‛‹@#›’
#define no_line_break		0x8d	// control code for ‛‹@+›’
#define pseudo_semi		0x8e	// control code for ‛‹@;›’
#define macro_arg_open		0x90	// control code for ‛‹@[›’
#define macro_arg_close		0x91	// control code for ‛‹@]›’
#define trace			0x92	// control code for ‛‹@0›’, ‛‹@1›’ and ‛‹@2›’
#define translit_code		0x93	// control code for ‛‹@l›’
#define output_defs_code	0x94	// control code for ‛‹@h›’
#define format_code		0x95	// control code for ‛‹@f›’ and ‛‹@s›’
#define definition		0x96	// control code for ‛‹@d›’
#define begin_C			0x97	// control code for ‛‹@c›’
#define section_name		0x98	// control code for ‛‹@<›’
#define new_section		0x99	// control code for ‛‹@ ›’ and ‛‹@*›’

// 1.2.2†1.2.7:
void skip_limbo(void) {
   while(1) {
      if (loc > limit ∧ get_line() ≡ 0) return;
      *(limit + 1) = '@';
      for (; *loc ≠ '@'; loc↑);	// look for '@', then skip two chars
      if (loc↑ ≤ limit) {
         int c = ccode[(eight_bits)*loc↑];
         if (c ≡ new_section) return;
         else if (c ≡ noop) skip_restricted();
         else if (c ≡ format_code) {
         // †2.0.14: Process simple format in limbo
         // A much simpler processing of format definitions occurs when the definition is found in limbo.
            if (get_next() ≠ identifier) err_print("! Missing left identifier of @s");	// ⁅011⁆
            else {
               lhs = id_lookup(id_first, id_loc, normal);
               if (get_next() ≠ identifier) err_print("! Missing right identifier of @s");	// ⁅012⁆
               else rhs = id_lookup(id_first, id_loc, normal), lhs→ilk = rhs→ilk;
            }
         // 2.0.14†
         }
      }
   }
}

// 1.2.7†1.2.8:
// The ≪skip_TeX≫ routine is used on the first pass to skip through the ‹TeX› code at the beginning of a section.
// It returns the next control code or ‛‹|›’ found in the input.
// A ≪new_section≫ is assumed to exist at the very end of the file.

// #format skip_TeX TeX
unsigned skip_TeX(void) {	// skip past pure ‹TeX› code
   while (1) {
      if (loc > limit ∧ get_line() ≡ 0) return new_section;
      *(limit + 1) = '@';
      for (; *loc ≠ '@' ∧ *loc ≠ '|'; loc↑);
      if (*loc↑ ≡ '≪') return '≫';
      if (loc ≤ limit) return ccode[(eight_bits)*loc↑];
   }
}
// 1.2.8†

// ‡1.3. Inputting the Next Token.
// †1.3.4:
eight_bits get_next(void) {	// produces the next input token
   while (1) {
   // †1.3.9: Check if we're at the end of a preprocessor command
   // When we get to the end of a preprocessor line, we lower the flag and send a code ≪right_preproc≫, unless the last character was a ‹\›.
      while (loc ≡ limit - 1 ∧ preprocessing ∧ *loc ≡ '\\')
         if (get_line() ≡ 0) return new_section;	// still in preprocessor mode
      if (loc ≥ limit ∧ preprocessing) {
         preprocessing = sharp_include_line = 0;
         return right_preproc;
      }
   // 1.3.9†
      if (loc > limit ∧ get_line() ≡ 0) return new_section;
      eight_bits c = *loc↑;	// the current character
      if (xisdigit(c) ∨ c ≡ '.') {
      // †1.3.12: Get a constant
      // Different conventions are followed by ‹TeX› and ‹C99› to express octal and hexadecimal numbers; it is reasonable to stick to each convention within its realm.
      // Thus the ‹C99› part of a ‹CWEB› file has octals introduced by ‹0› and hexadecimals by ‹0x›,
      // but ‹CWEAVE› will print with ‹TeX› macros that the user can redefine to fit the context.
      // In order to simplify such macros, we replace some of the characters.
      //
      // Notice that in this section and the next, ≪id_first≫ and ≪id_loc≫ are pointers into the array ≪section_text≫, not into ≪buffer≫.
         id_first = id_loc = section_text + 1;
         if (*(loc - 1) ≡ '0') {
            if (*loc ≡ 'x' ∨ *loc ≡ 'X')	// hex constant
               for (*id_loc↑ = '^', loc↑; xisxdigit(*loc); *id_loc↑ = *loc↑);
            else if (xisdigit(*loc))	// octal constant
               for (*id_loc↑ = '~'; xisdigit(*loc); *id_loc↑ = *loc↑);
            else goto dec;	// decimal constant
         } else {	// decimal constant
            if (*(loc - 1) ≡ '.' ∧ !xisdigit(*loc)) goto mistake;	// not a constant
         dec:
            for (*id_loc↑ = *(loc - 1); xisdigit(*loc) ∨ *loc ≡ '.'; *id_loc↑ = *loc↑);
            if (*loc ≡ 'e' ∨ *loc ≡ 'E') {	// float constant
               *id_loc↑ = '_', loc↑;
               if (*loc ≡ '+' ∨ *loc ≡ '-') *id_loc↑ = *loc↑;
               for (; xisdigit(*loc); *id_loc↑ = *loc↑);
            }
         }
         while (*loc ≡ 'u' ∨ *loc ≡ 'U' ∨ *loc ≡ 'l' ∨ *loc ≡ 'L' ∨ *loc ≡ 'f' ∨ *loc ≡ 'F') *id_loc↑ = '$', *id_loc↑ = toupper(*loc↑);
      // 1.3.12†
         return constant;
      } else if (c ≡ '\'' ∨ c ≡ '"' ∨ (c ≡ 'L' ∧ (*loc ≡ '\'' ∨ *loc ≡ '"')) ∨ c ≡ '<' ∧ sharp_include_line ≡ 1) {
      // †1.3.13: [2] Get a string
      // ‹C99› strings and character constants, delimited by double and single quotes, respectively,
      // can contain newlines or instances of their own delimiters if they are protected by a backslash.
      // We follow this convention, but do not allow the string to be longer than ≪longest_name≫.
         char delim = c;	// what started the string
         id_first = section_text + 1, id_loc = section_text;
         if (delim ≡ '\'' ∧ *(loc - 2) ≡ '@') *↑id_loc = '@', *↑id_loc = '@';
         *↑id_loc = delim;
         if (delim ≡ 'L')	// wide character constant
            delim = *loc↑, *↑id_loc = delim;
         if (delim ≡ '<') delim = '>';	// for file names in ≪#include≫ lines
         while (1) {
            if (loc ≥ limit) {
               if (*(limit - 1) ≠ '\\') {
                  err_print("! String didn't end"), loc = limit; break;	// ⁅013⁆
               }
               if (get_line() ≡ 0) {
                  err_print("! Input ended in middle of string"), loc = buffer; break;	// ⁅014⁆
               }
            }
            c = *loc↑;
            if (c ≡ delim) {
               if (↑id_loc ≤ section_text_end) *id_loc = c;
               break;
            }
            if (c ≡ '\\')
               if (loc ≥ limit) continue;
               else if (↑id_loc ≤ section_text_end) *id_loc = '\\', c = *loc↑;
            if (↑id_loc ≤ section_text_end) *id_loc = c;
         }
         if (id_loc ≥ section_text_end) printf("\n! String too long: "), term_write(section_text + 1, 25), printf("..."), mark_error();	// ⁅015⁆
         id_loc↑;
      // 1.3.13†
         return string;
      } else if (xisalpha(c) ∨ isxalpha(c) ∨ ishigh(c)) {
      // †1.3.11: Get an identifier
         id_first = ↓loc;
         while (isalpha(*↑loc) ∨ isdigit(*loc) ∨ isxalpha(*loc) ∨ ishigh(*loc));
         id_loc = loc;
      // 1.3.11†
         return identifier;
      } else if (c ≡ '@') {
      // †1.3.14: Get control code and possible section name
      // After an ‹@› sign has been scanned, the next character tells us whether there is more work to do.
         c = *loc↑;
         switch (ccode[(eight_bits)c]) {
            case translit_code: err_print("! Use @l in limbo only"); continue;	// ⁅016⁆
            case underline: xref_switch = def_flag; continue;
            case trace: tracing = c - '0'; continue;
            case xref_roman: case xref_wildcard: case xref_typewriter:
            case noop: case TeX_string: c = ccode[c], skip_restricted(); return c;
            case section_name: {
            // †1.3.15: Scan the section name and make ≪cur_section≫ point to it
            // The occurrence of a section name sets ≪xref_switch≫ to zero, because the section name might (for example) follow «int».
               cur_section_char = *(loc - 1);
               char *k;	// pointer into ≪section_text≫
            // †1.3.17: Put section name into ≪section_text≫
               k = section_text;
               while (1) {
                  if (loc > limit ∧ get_line() ≡ 0) {
                     err_print("! Input ended in section name");	// ⁅017⁆
                     loc = buffer + 1; break;
                  }
                  c = *loc;
               // †1.3.18: If end of name or erroneous control code, ≪break≫
                  if (c ≡ '@') {
                     c = *(loc + 1);
                     if (c ≡ '>') { loc += 2; break; }
                     if (ccode[(eight_bits)c] ≡ new_section) {
                        err_print("! Section name didn't end"); break;	// ⁅018⁆
                     }
                     if (c ≠ '@') {
                        err_print("! Control codes are forbidden in section name"); break;	// ⁅019⁆
                     }
                     *↑k = '@', loc↑;	// now ≪c ≡ *loc≫ again
                  }
               // 1.3.18†
                  loc↑; if (k < section_text_end) k↑;
                  if (xisspace(c)) {
                     c = ' '; if (*(k - 1) ≡ ' ') k↓;
                  }
                  *k = c;
               }
               if (k ≥ section_text_end)
                  printf("\n! Section name too long: "),	// ⁅020⁆
                  term_write(section_text + 1, 25), printf("..."), mark_harmless();
               if (*k ≡ ' ' ∧ k > section_text) k↓;
            // 1.3.17†
               cur_section = k - section_text > 3 ∧ strncmp(k - 2, "...", 3) ≡ 0?
                  section_lookup(section_text + 1, k - 3, 1):	// 1 indicates a prefix
                  section_lookup(section_text + 1, k, 0);
               xref_switch = 0;
            // 1.3.15†
               return section_name;
            }
            case verbatim: {
            // †1.3.21: Scan a verbatim string
            // At the present point in the program we have ≪*(loc - 1) ≡ verbatim≫;
            // we set ≪id_first≫ to the beginning of the string itself, and ≪id_loc≫ to its ending-plus-one location in the buffer.
            // We also set ≪loc≫ to the position just after the ending delimiter.
               id_first = loc↑, *(limit + 1) = '@', *(limit + 2) = '>';
               for (; *loc ≠ '@' ∨ *(loc + 1) ≠ '>'; loc↑);
               if (loc ≥ limit) err_print("! Verbatim string didn't end");	// ⁅021⁆
               id_loc = loc, loc += 2;
            // 1.3.21†
               return verbatim;
            }
            case ord: {
               ≪≪†1.3.13: [2] Get a string≫≫ // ;
               return string;
            }
            default: return ccode[(eight_bits)c];
         }
      // 1.3.14†
      } else if (xisspace(c)) continue;	// ignore spaces and tabs
      if (c ≡ '#' ∧ loc ≡ buffer + 1) {
      // †1.3.6: Raise preprocessor flag
         preprocessing = 1;
      // †1.3.8: Check if next token is ≪include≫
         for (; loc ≤ buffer_end - 7 ∧ xisspace(*loc); loc↑);
         if (loc ≤ buffer_end - 6 ∧ strncmp(loc, "include", 7) ≡ 0) sharp_include_line = 1;
      // 1.3.8†
      // 1.3.6†
         return left_preproc;
      }
   mistake:
   // †1.3.10: Compress two-symbol operator
   // The following code assigns values to the combinations ‹++›, ‹--›, ‹->›, ‹>=›, ‹<=›, ‹==›, ‹<<›, ‹>>›, ‹!=›, ‹||›, and ‹&&›,
   // and to the ‹C++› combinations ‹...›, ‹::›, ‹.*› and ‹->*›.
   // The compound assignment operators (e.g., ‹+=›) are treated as separate tokens.
#define compress(c) if (loc↑ ≤ limit) return c
      switch (c) {
         case '/': switch (*loc) {
            case '*': compress(begin_comment); break;
            case '/': compress(begin_short_comment); break;
         }
         break;
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
            case '<': compress(lt_lt); break;
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
            case '='; compress(not_eq); break;
         }
         break;
      }
   // 1.3.10†
      return c;
   }
}

// 1.3.4†1.3.20:
void skip_restricted(void) {
   id_first = loc, *(limit + 1) = '@';
false_alarm:
   for (; *loc ≠ '@'; loc↑);
   id_loc = loc;
   if (loc↑ > limit) err_print("! Control text didn't end"), loc = limit;	// ⁅022⁆
   else if (*loc ≡ '@' ∧ loc ≤ limit) { loc↑; goto false_alarm; }
   else if (*loc↑ ≠ '>') err_print("! Control codes are forbidden in control text");	// ⁅023⁆
}
// 1.3.20†

// §2. Phase One Processing.
// †2.0.3:
void phase_one(void) {
   phase = 1, reset_input(), section_count = 0;
   skip_limbo(), change_exists = 0;
   while (!input_has_ended) {
   // †2.0.4: Store cross-reference data for the current section
      if (↑section_count ≡ max_sections) overflow("section number");
      changed_section[section_count] = changing;	// it will become 1 if any line changes
      if (*(loc - 1) ≡ '*' ∧ show_progress) printf("*%d", section_count), update_terminal();	// print a progress report
   // †2.0.9: Store cross-references in the ‹TeX› part of a section
   // In the ‹TeX› part of a section, cross-reference entries are made only for the identifiers in ‹C99› texts enclosed in ‹pb›,
   // or for control texts enclosed in ‹@^› … ‹@>› or ‹@.› … ‹@>› or ‹@:› … ‹@>›.
      while (1) {
         switch (next_control = skip_TeX()) {
            case translit_code: err_print("! Use @l in limbo only"); continue;	// ⁅024⁆
            case underline: xref_switch = def_flag; continue;
            case trace: tracing = *(loc - 1) - '0'; continue;
            case '|': C_xref(section_name); break;
            case xref_roman: case xref_wildcard: case xref_typewriter:
            case noop: case section_name:
               loc -= 2, next_control = get_next();	// scan to ‹@>›
               if (next_control ≥ xref_roman ∧ next_control ≤ xref_typewriter)
                  CompressAt(),	// Replace ≪"@@"≫ by ≪"@"≫ ≫≫
                  new_xref(id_lookup(id_first, id_loc, next_control-identifier));
            break;
         }
         if (next_control ≥ format_code) break;
      }
   // 2.0.9†2.0.12: Store cross-references in the definition part of a section
   // When we get to the following code we have ≪next_control ≥ format_code≫.
      while (next_control ≤ definition) {	// ≪format_code≫ or ≪definition≫
         if (next_control ≡ definition)
            xref_switch = def_flag,	// implied ‹@!›
            next_control = get_next();
         else {
         // †2.0.13: Process a format definition
         // Error messages for improper format definitions will be issued in phase two.
         // Our job in phase one is to define the ≪ilk≫ of a properly formatted identifier,
         // and to remove cross-references to identifiers that we now discover should be unindexed.
            next_control = get_next();
            if (next_control ≡ identifier) {
               lhs = id_lookup(id_first, id_loc, normal), lhs→ilk = normal;
               if (xref_switch) new_xref(lhs);
               next_control = get_next();
               if (next_control ≡ identifier) {
                  rhs = id_lookup(id_first, id_loc, normal), lhs→ilk = rhs→ilk;
                  if (unindexed(lhs)) {	// retain only underlined entries
                     xref_pointer q, r = NULL;
                     for (q = (xref_pointer)lhs→xref; q > xmem; q = q→xlink)
                        if (q→num ≥ def_flag) r = q;
                        else if (r ≠ NULL) r→xlink = q→xlink;
                        else lhs→xref = (char *)q→xlink;
                  }
                  next_control = get_next();
               }
            }
         // 2.0.13†
         }
         outer_xref();
      }
   // 2.0.12†2.0.15: Store cross-references in the ‹C99› part of a section
   // Finally, when the ‹TeX› and definition parts have been treated, we have ≪next_control ≥ begin_C≫.
      if (next_control ≤ section_name) {	// ≪begin_C≫ or ≪section_name≫
         if (next_control ≡ begin_C) section_xref_switch = 0;
         else {
            section_xref_switch = def_flag;
            if (cur_section_char ≡ '(' ∧ cur_section ≠ name_dir) set_file_flag(cur_section);
         }
         do {
            if (next_control ≡ section_name ∧ cur_section ≠ name_dir) new_section_xref(cur_section);
            next_control = get_next(), outer_xref();
         } while (next_control ≤ section_name);
      }
   // 2.0.15†
      if (changed_section[section_count]) change_exists = 1;
   // 2.0.4†
   }
   changed_section[section_count] = change_exists;	// the index changes if anything does
   phase = 2;	// prepare for second phase
// †2.0.19: Print error messages about unused or undefined section names
   section_check(root)
// 2.0.19†
}

// 2.0.3†2.0.6:
void C_xref(eight_bits spec_ctrl) {	// makes cross-references for ‹C99› identifiers
   while (next_control < format_code ∨ next_control ≡ spec_ctrl) {
      if (next_control ≥ identifier ∧ next_control ≤ xref_typewriter) {
         if (next_control > identifier) CompressAt();	// Replace ≪"@@"≫ by ≪"@"≫ ≫≫
         new_xref(id_lookup(id_first, id_loc, next_control - identifier));	// a newly-referenced name
      }
      if (next_control ≡ section_name) section_xref_switch = cite_flag, new_section_xref(cur_section);
      next_control = get_next();
      if (next_control ≡ '|' ∨ next_control ≡ begin_comment ∨ next_control ≡ begin_short_comment) return;
   }
}

// 2.0.6†2.0.8:
void outer_xref(void) {	// extension of ≪C_xref≫
   while (next_control < format_code)
      if (next_control ≠ begin_comment ∧ next_control ≠ begin_short_comment) C_xref(ignore);
      else {
         boolean is_long_comment = next_control ≡ begin_comment;
         int bal = copy_comment(is_long_comment, 1);	// brace level in comment
         next_control = '|';
         while (bal > 0) {
            C_xref(section_name);	// do not reference section names in comments
            if (next_control ≠ '|') { bal = 0; break; }	// an error message will occur in phase two
            bal = copy_comment(is_long_comment, bal);
         }
      }
}

// 2.0.8†2.0.10: [2] Replace ≪"@@"≫ by ≪"@"≫
// Editor's Note:
// ∙	This was orginally a multiply-used module.
inline void CompressAt(void) {
   char *src = id_first, *dst = id_first;
   for (; src < id_loc *dst↑ = *src↑) if (*src ≡ '@') src↑;
   id_loc = dst;
   for (; dst < src; *dst↑ = ' ');	// clean up in case of error message display
}

// 2.0.10†2.0.18:
void section_check(name_pointer p) { 	// print anomalies in subtree ≪p≫
   if (p ≠ NULL) {
      section_check(p→llink);
      cur_xref = (xref_pointer)p→xref;
      if (cur_xref→num ≡ file_flag) an_output = 1, cur_xref = cur_xref→xlink; else an_output = 0;
      if (cur_xref→num < def_flag)
         printf("\n! Never defined: <"), print_section_name(p), putchar('>'), mark_harmless();	// ⁅025⁆
      for (; cur_xref→num ≥ cite_flag; cur_xref = cur_xref→xlink);
      if (cur_xref ≡ xmem ∧ !an_output) printf("\n! Never used: <"), print_section_name(p), putchar('>'), mark_harmless();	// ⁅026⁆
      section_check(p→rlink);
   }
}
// 2.0.18†

// ‡2.1. Low-Level Output Routines.
// †2.1.2:
// The ≪flush_buffer≫ routine empties the buffer up to a given breakpoint, and moves any remaining characters to the beginning of the next line.
// If the ≪per_cent≫ parameter is 1 a ≪'%'≫ is appended to the line that is being output; in this case the breakpoint ≪b≫ should be strictly less than ≪out_buf_end≫.
// If the ≪per_cent≫ parameter is ≪0≫, trailing blanks are suppressed.
// The characters emptied from the buffer form a new line of output;
// if the ≪carryover≫ parameter is true, a ≪"%"≫ in that line will be carried over to the next line (so that ‹TeX› will ignore the completion of commented-out text).
#define c_line_write(c) fflush(active_file), fwrite(out_buf + 1, sizeof(char), c, active_file)
#define tex_putc(c) putc(c, active_file)
#define tex_new_line() putc('\n', active_file)
#define tex_printf(c) fprintf(active_file, c)

// b: outputs from ≪out_buf + 1≫ to ≪b≫, where ≪b ≤ out_ptr≫
void flush_buffer(char *b, boolean per_cent, boolean carryover) {
   char *j = b;	// pointer into ≪out_buf≫
   if (!per_cent) for (; j > out_buf ∧ *j ≡ ' '; j↓);	// remove trailing blanks
   c_line_write(j - out_buf);
   if (per_cent) tex_putc('%');
   tex_new_line(), out_line↑;
   if (carryover)
      while (j > out_buf) if (*j↓ ≡ '%' ∧ (j ≡ out_buf ∨ *j ≠ '\\')) { *b↓ = '%'; break; }
   if (b < out_ptr) strncpy(out_buf + 1, b + 1, out_ptr - b);
   out_ptr -= b-out_buf;
}

// 2.1.2†2.1.3:
// When we are copying ‹TeX› source material, we retain line breaks that occur in the input,
// except that an empty line is not output when the ‹TeX› source line was nonempty.
// For example, a line of the ‹TeX› file that contains only an index cross-reference entry will not be copied.
// The ≪finish_line≫ routine is called just before ≪get_line≫ inputs a new line,
// and just after a line break token has been emitted during the output of translated ‹C99› text.
void finish_line(void) {	// do this at the end of a line
   if (out_ptr > out_buf) flush_buffer(out_ptr, 0, 0);
   else {
      for (char *k = buffer; k ≤ limit; k↑) if (!xisspace(*k)) return;
      flush_buffer(out_buf, 0, 0);
   }
}

// 2.1.3†2.1.5:
// When we wish to append one character ≪c≫ to the output buffer, we write ‛≪out(c)≫’; this will cause the buffer to be emptied if it was already full.
// If we want to append more than one character at once, we say ≪out_str(s)≫, where ≪s≫ is a string containing the characters.

// A line break will occur at a space or after a single-nonletter ‹TeX› control sequence.
#define out(c) {
   if (out_ptr ≥ out_buf_end) break_out();
   *↑out_ptr = c;
}

void out_str(char *s) {	// output characters from ≪s≫ to end of string
   while (*s ≠ '\0') out(*s↑);
}

// 2.1.5†2.1.8:
void break_out(void) {	// finds a way to break the output line
   char *k = out_ptr;	// pointer into ≪out_buf≫
   while (1) {
      if (k ≡ out_buf) {
      // †2.1.9: Print warning message, break the line
      // We get to this section only in the unusual case that the entire output line consists of a string of backslashes followed by a string of nonblank non-backslashes.
      // In such cases it is almost always safe to break the line by putting a ≪'%'≫ just before the last character.
         printf("\n! Line had to be broken (output l. %d):\n", out_line);	// ⁅027⁆
         term_write(out_buf + 1, out_ptr - out_buf - 1);
         new_line(), mark_harmless();
         flush_buffer(out_ptr - 1, 1, 1);
      // 2.1.9†
         break;
      } else if (*k ≡ ' ') { flush_buffer(k, 0, 1); break; }
      else if (*k↓ ≡ '\\' ∧ *k ≠ '\\') {	// we've decreased ≪k≫
         flush_buffer(k, 1, 1); break;
      }
   }
}

// 2.1.8†2.1.10:
// Here is a macro that outputs a section number in decimal notation.
// The number to be converted by ≪out_section≫ is known to be less than ≪def_flag≫, so it cannot have more than five decimal digits.
// If the section is changed, we output ‛‹\*›’ just after the number.
void out_section(sixteen_bits n) {
   char s[6]; sprintf(s, "%d", n), out_str(s);
   if (changed_section[n]) out_str("\\*");	// ⁅028⁆
}

// 2.1.10†2.1.11:
// The ≪out_name≫ procedure is used to output an identifier or index entry, enclosing it in braces.
void out_name(name_pointer p, boolean quote_xalpha) {
   char *k_end = (p + 1)→byte_start;	// pointers into ≪byte_mem≫
   out('{');
   for (char *k = p→byte_start; k < k_end; k↑) {
      if (isxalpha(*k) ∧ quote_xalpha) out('\\');	// ⁅029⁆⁅030⁆
      out(*k);
   }
   out('}');
}
// 2.1.11†

// ‡2.2. Routines That Copy ‹TeX› Material.
// †2.2.1:
// During phase two, we use subroutines ≪copy_limbo≫, ≪copy_TeX≫, and ≪copy_comment≫ in place of the analogous ≪skip_limbo≫, ≪skip_TeX≫,
// and ≪skip_comment≫ that were used in phase one.
// (Well, ≪copy_comment≫ was actually written in such a way that it functions as ≪skip_comment≫ in phase one.)

// The ≪copy_limbo≫ routine, for example, takes ‹TeX› material that is not part of any section and transcribes it almost verbatim to the output file.
// The use of ‛‹@›’ signs is severely restricted in such material: ‛‹@@›’ pairs are replaced by singletons; ‛‹@l›’ and ‛‹@q›’ and ‛‹@s›’ are interpreted.
void copy_limbo(void) {
   while (1) {
      if (loc > limit ∧ (finish_line(), get_line() ≡ 0)) break;
      *(limit + 1) = '@';
      while (*loc ≠ '@') out(*loc↑);
      if (loc↑ ≤ limit) {
         char c = *loc↑;
         if (ccode[(eight_bits)c] ≡ new_section) break;
         switch (ccode[(eight_bits)c]) {
            case translit_code: out_str("\\ATL"); break;	// ⁅031⁆
            case '@': out('@'); break;
            case noop: skip_restricted(); break;
            case format_code:
               if (get_next() ≡ identifier) get_next();
               if (loc ≥ limit) get_line();	// avoid blank lines in output
            break;	// the operands of ‹@s› are ignored on this pass
            default:
               err_print("! Double @ should be used in limbo");	// ⁅032⁆
               out('@');
            break;
         }
      }
   }
}

// 2.2.1†2.2.2:
// The ≪copy_TeX≫ routine processes the ‹TeX› code at the beginning of a section; for example, the words you are now reading were copied in this way.
// It returns the next control code or ‛‹|›’ found in the input.
// We don't copy spaces or tab marks into the beginning of a line.
// This makes the test for empty lines in ≪finish_line≫ work.

// 2.2.2†2.2.3:
// #format copy_TeX TeX
eight_bits copy_TeX(void) {
   while (1) {
      if (loc > limit ∧ (finish_line(), get_line() ≡ 0)) return new_section;
      *(limit + 1) = '@';
      char c;	// current character being copied
      while ((c = *loc↑) ≠ '|' ∧ c ≠ '@') {
         out(c);
         if (out_ptr ≡ out_buf + 1 ∧ (xisspace(c))) out_ptr↓;
      }
      if (c ≡ '|') return '|';
      if (loc ≤ limit) return ccode[(eight_bits)*(loc↑)];
   }
}

// 2.2.3†2.2.5:
// is_long_comment: is this a traditional ‹C99› comment?
// bal: brace balance
int copy_comment(boolean is_long_comment, int bal) {	// copies ‹TeX› code in comments
   while (1) {
      if (loc > limit) {
         if (is_long_comment) {
            if (get_line() ≡ 0) {
               err_print("! Input ended in mid-comment");	// ⁅033⁆
               loc = buffer + 1; break;
            }
         } else {
            if (bal > 1) err_print("! Missing } in comment");	// ⁅034⁆
            break;
         }
      }
      char c = *loc↑;	// current character being copied
      if (c ≡ '|') return bal;
      if (is_long_comment)
      // †2.2.6: Check for end of comment
         if (c ≡ '*' ∧ *loc ≡ '/') {
            loc↑;
            if (bal > 1) err_print("! Missing } in comment");	// ⁅035⁆
            break;
         }
      // 2.2.6†
      if (phase ≡ 2) {
         if (ishigh(c)) app_tok(quoted_char);
         app_tok(c);
      }
   // †2.2.7: Copy special things when ≪c ≡ '@', '\\'≫
      if (c ≡ '@') {
         if (*loc↑ ≠ '@') {
            err_print("! Illegal use of @ in comment");	// ⁅036⁆
            loc -= 2; if (phase ≡ 2) *(tok_ptr - 1) = ' '; break;
         }
      } else if (c ≡ '\\' ∧ *loc ≠ '@')
         if (phase ≡ 2) app_tok(*loc↑); else loc↑;
   // 2.2.7†
      if (c ≡ '{') bal↑;
      else if (c ≡ '}') {
         if (bal > 1) bal↓;
         else {
            err_print("! Extra } in comment");	// ⁅037⁆
            if (phase ≡ 2) tok_ptr↓;
         }
      }
   }
// †2.2.8: Clear ≪bal≫
// We output enough right braces to keep ‹TeX› happy.
   if (phase ≡ 2) while (bal↓ > 0) app_tok('}');
// 2.2.8†
   return 0;
}
// 2.2.5†

// §3. Parsing.
// †3.0.1:
// The most intricate part of ‹CWEAVE› is its mechanism for converting ‹C99›-like code into ‹TeX› code, and we might as well plunge into this aspect of the program now.
// A ‟bottom up” approach is used to parse the ‹C99›-like material, since ‹CWEAVE› must deal with fragmentary constructions whose overall ‟part of speech” is not known.

// At the lowest level, the input is represented as a sequence of entities that we shall call ≪_ scraps _≫,
// where each scrap of information consists of two parts, its ≪_ category _≫ and its ≪_ translation _≫.
// The category is essentially a syntactic class, and the translation is a token list that represents ‹TeX› code.
// Rules of syntax and semantics tell us how to combine adjacent scraps into larger ones,
// and if we are lucky an entire ‹C99› text that starts out as hundreds of small scraps
// will join together into one gigantic scrap whose translation is the desired ‹TeX› code.
// If we are unlucky, we will be left with several scraps that don't combine; their translations will simply be output, one by one.

// The combination rules are given as context-sensitive productions that are applied from left to right.
// To resolve ambiguity:
// ∙	if two or more rules match, then the one(s) with the shortest left context is applied,
// ∙	if two or more of these rules match, then the longest one(s) is applied, and
// ∙	if two or more of these rules match, then the first one listed is applied.
// Suppose that we are currently working on the sequence of scraps s₀ s₁ … s_n.
// We try first to find the longest production that applies to an initial substring s₀ s₁ …;
// but if no such productions exist, we try to find the longest production applicable to the next substring s₁ s₂ … ;
// and if that fails, we try to match s₂ s₃ … , etc.

// A production applies if the category codes have a given pattern.
// For example, one of the productions (see rule 3) is
//	≪exp≫	┌ ≪binop≫	┐ ≪exp≫	⇐	≪exp≫
//		└ ≪ubinop≫	┘
// and it means that three consecutive scraps whose respective categories are ≪exp≫, ≪binop≫ (or ≪ubinop≫), and ≪exp≫ are converted to one scrap whose category is ≪exp≫.
// The translations of the original scraps are simply concatenated.
// The case of
//	≪exp≫ ≪comma≫ ≪exp≫	⇐	≪exp≫ E₀ C «opt»9 E₁
// (rule 4) is only slightly more complicated:
// Here the resulting ≪exp≫ translation consists not only of the three original translations,
// but also of the tokens ≪opt≫ and 9 between the translations of the ≪comma≫ and the following ≪exp≫.
// In the ‹TeX› file, this will specify an optional line break after the comma, with penalty 90.

// At each opportunity the longest possible production is applied.
// For example, if the current sequence of scraps is ≪int_like≫ ≪cast≫ ≪lbrace≫, rule 31 is applied;
// but if the sequence is ≪int_like≫ ≪cast≫ followed by anything other than ≪lbrace≫, rule 32 takes effect.

// Translation rules such as ‛E₀ C «opt»9 E₁’ above use subscripts to distinguish between translations of scraps whose categories have the same initial letter;
// these subscripts are assigned from left to right.

// 3.0.1†3.0.4:
// This code allows ‹CWEAVE› to display its parsing steps.
void print_cat(eight_bits c) {	// symbolic printout of a category
   printf(cat_name[c]);
}

// 3.0.4†3.0.5:
// The token lists for translated ‹TeX› output contain some special control
// symbols as well as ordinary characters. These control symbols are
// interpreted by ‹CWEAVE› before they are written to the output file.
// ∙	≪break_space≫ denotes an optional line break or an en space;
// ∙	≪force≫ denotes a line break;
// ∙	≪big_force≫ denotes a line break with additional vertical space;
// ∙	≪preproc_line≫ denotes that the line will be printed flush left;
// ∙	≪opt≫ denotes an optional line break (with the continuation line indented two ems with respect to the normal starting position) ―
//	this code is followed by an integer ≪n≫, and the break will occur with penalty 10n;
// ∙	≪backup≫ denotes a backspace of one em;
// ∙	≪cancel≫ obliterates any ≪break_space≫, ≪opt≫, ≪force≫, or ≪big_force≫ tokens
//	that immediately precede or follow it and also cancels any ≪backup≫ tokens that follow it;
// ∙	≪indent≫ causes future lines to be indented one more em;
// ∙	≪outdent≫ causes future lines to be indented one less em.
// All of these tokens are removed from the ‹TeX› output that comes from ‹C99› text between ‹pb› signs;
// ≪break_space≫ and ≪force≫ and ≪big_force≫ become single spaces in this mode.
// The translation of other ‹C99› texts results in ‹TeX› control sequences ‹\1›, ‹\2›, ‹\3›, ‹\4›, ‹\5›, ‹\6›, ‹\7›, ‹\8›
// corresponding respectively to ≪indent≫, ≪outdent≫, ≪opt≫, ≪backup≫, ≪break_space≫, ≪force≫, ≪big_force≫ and ≪preproc_line≫.
// However, a sequence of consecutive ‛‹ ›’, ≪break_space≫, ≪force≫, and/or ≪big_force≫ tokens is first replaced by a single token (the maximum of the given ones).

// The token ≪math_rel≫ will be translated into ‹\MRL{›, and it will get a matching ‹}› later.
// Other control sequences in the ‹TeX› output will be
//	‛‹\\{› … ‹}›’ surrounding identifiers,
//	‛‹\&{› … ‹}›’ surrounding reserved words,
//	‛‹\.{› … ‹}›’ surrounding strings,
//	‛‹\C{› … ‹} ≪force≫’ surrounding comments, and
//	‛‹\Xn:› … ‹\X›’ surrounding section names, where ≪n≫ is the section number.
#define math_rel	0x86
#define big_cancel	0x88	// like ≪cancel≫, also overrides spaces
#define cancel		0x89	// overrides ≪backup≫, ≪break_space≫, ≪force≫, ≪big_force≫
#define indent		0x8a	// one more tab (‹\1›)
#define outdent		0x8b	// one less tab (‹\2›)
#define opt		0x8c	// optional break in mid-statement (‹\3›)
#define backup		0x8d	// stick out one unit to the left (‹\4›)
#define break_space	0x8e	// optional break between statements (‹\5›)
#define force		0x8f	// forced break between statements (‹\6›)
#define big_force	0x90	// forced break with additional space (‹\7›)
#define preproc_line	0x91	// begin line without indentation (‹\8›) ⁅038⁆
#define quoted_char	0x92	// introduces a character token in the range ≪0x80≫―≪0377≫
#define end_translation	0x93	// special sentinel token at end of list
#define inserted	0x94	// sentinel to mark translations of inserts
#define qualifier	0x95	// introduces an explicit namespace qualifier

// 3.0.5†3.0.6:
// The raw input is converted into scraps according to the following table, which gives category codes followed by the translations.
// The symbol ‛‹**›’ stands for ‛‹\&{identifier}›’, i.e., the identifier itself treated as a reserved word.
// The left-hand column is the so-called ≪mathness≫, which is explained further below.

// An identifier ≪c≫ of length 1 is translated as ‹\|c› instead of as ‹\\{c}›.
// An identifier ‹CAPS› in all caps is translated as ‹\.{CAPS}› instead of as ‹\\{CAPS}›.
// An identifier that has become a reserved word via ≪typedef≫ is translated with ‹\&› replacing ‹\\› and ≪raw_int≫ replacing ≪exp≫.

// A string of length greater than 20 is broken into pieces of size at most 20 with discretionary breaks in between.
//	yes	‹!=›				⇐ binop‹\I›
//	yes	‹<=›				⇐ binop‹\Z›
//	yes	‹>=›				⇐ binop‹\G›
//	yes	‹==›				⇐ binop‹\E›
//	yes	‹&&›				⇐ binop‹\W›
//	yes	‹||›				⇐ binop‹\V›
//	yes	‹++›				⇐ unop‹\PP›
//	yes	‹--›				⇐ unop‹\MM›
//	yes	‹->›				⇐ binop‹\MG›
//	yes	‹>>›				⇐ binop‹\GG›
//	yes	‹<<›				⇐ binop‹\LL›
//	maybe	‹::›				⇐ colcol‹\DC›
//	yes	‹.*›				⇐ binop‹\PA›
//	yes	‹->*›				⇐ binop‹\MGA›
//	yes	‹...›				⇐ raw_int‹\,\ldots\,›
//	maybe	‹"›string‹"›			⇐ exp‹\.{›string with special characters quoted‹}›
//	maybe	‹@=›string‹@>›			⇐ exp‹\vb{›string with special characters quoted‹}›
//	maybe	‹@'7'›				⇐ exp‹\.{@'7'}›
//	maybe	‹077› or ‹\77›			⇐ exp‹\T{\~77}›
//	maybe	‹0x7f›				⇐ exp‹\T{\^7f}›
//	maybe	‹77›				⇐ exp‹\T{77}›
//	maybe	‹77L›				⇐ exp‹\T{77\$L}›
//	maybe	‹0.1E5›				⇐ exp‹\T{0.1\_5}›
//	yes	‹+›				⇐ ubinop‹+›
//	yes	‹-›				⇐ ubinop‹-›
//	yes	‹*›				⇐ raw_ubin‹*›
//	yes	‹/›				⇐ binop‹/›
//	yes	‹<›				⇐ prelangle‹\langle›
//	yes	‹=›				⇐ binop‹\K›
//	yes	‹>›				⇐ prerangle‹\rangle›
//	yes	‹.›				⇐ binop‹.›
//	yes	‹|›				⇐ binop‹\OR›
//	yes	‹^›				⇐ binop‹\XOR›
//	yes	‹%›				⇐ binop‹\MOD›
//	yes	‹?›				⇐ question‹\?›
//	yes	‹!›				⇐ unop‹\R›
//	yes	‹~›				⇐ unop‹\CM›
//	yes	‹&›				⇐ raw_ubin‹\AND›
//	maybe	‹(›				⇐ lpar‹(›
//	maybe	‹[›				⇐ lpar‹[›
//	maybe	‹)›				⇐ rpar‹)›
//	maybe	‹]›				⇐ rpar‹]›
//	yes	‹{›				⇐ lbrace‹{›
//	yes	‹}›				⇐ lbrace‹}›
//	yes	‹,›				⇐ comma‹,›
//	maybe	‹;›				⇐ semi‹;›
//	no	‹:›				⇐ colon‹:›
//	yes	‹#› (within line)		⇐ ubinop‹\#›
//	no	‹#› (at beginning)		⇐ lproc‹≪force≫ ≪preproc_line≫ \#›
//	no	end of ‹#› line			⇐ rproc‹≪force≫›
//	maybe	identifier			⇐ exp‹‹\\{›identifier with underlines and dollar signs quoted‹}››
//	yes	‹and›				⇐ alfop‹**›
//	yes	‹and_eq›			⇐ alfop‹**›
//	maybe	‹asm›				⇐ sizeof_like‹**›
//	maybe	‹auto›				⇐ int_like‹**›
//	yes	‹bitand›			⇐ alfop‹**›
//	yes	‹bitor›				⇐ alfop‹**›
//	maybe	‹bool›				⇐ raw_int‹**›
//	maybe	‹break›				⇐ case_like‹**›
//	maybe	‹case›				⇐ case_like‹**›
//	maybe	‹catch›				⇐ catch_like‹**›
//	maybe	‹char›				⇐ raw_int‹**›
//	maybe	‹class›				⇐ struct_like‹**›
//	maybe	‹clock_t›			⇐ raw_int‹**›
//	yes	‹compl›				⇐ alfop‹**›
//	maybe	‹const›				⇐ const_like‹**›
//	maybe	‹const_cast›			⇐ raw_int‹**›
//	maybe	‹continue›			⇐ case_like‹**›
//	maybe	‹default›			⇐ case_like‹**›
//	maybe	‹define›			⇐ define_like‹**›
//	maybe	‹defined›			⇐ sizeof_like‹**›
//	maybe	‹delete›			⇐ delete_like‹**›
//	maybe	‹div_t›				⇐ raw_int‹**›
//	maybe	‹do›				⇐ do_like‹**›
//	maybe	‹double›			⇐ raw_int‹**›
//	maybe	‹dynamic_cast›			⇐ raw_int‹**›
//	maybe	‹elif›				⇐ if_like‹**›
//	maybe	‹else›				⇐ else_like‹**›
//	maybe	‹endif›				⇐ if_like‹**›
//	maybe	‹enum›				⇐ struct_like‹**›
//	maybe	‹error›				⇐ if_like‹**›
//	maybe	‹explicit›			⇐ int_like‹**›
//	maybe	‹export›			⇐ int_like‹**›
//	maybe	‹extern›			⇐ int_like‹**›
//	maybe	‹FILE›				⇐ raw_int‹**›
//	maybe	‹float›				⇐ raw_int‹**›
//	maybe	‹for›				⇐ for_like‹**›
//	maybe	‹fpos_t›			⇐ raw_int‹**›
//	maybe	‹friend›			⇐ int_like‹**›
//	maybe	‹goto›				⇐ case_like‹**›
//	maybe	‹if›				⇐ if_like‹**›
//	maybe	‹ifdef›				⇐ if_like‹**›
//	maybe	‹ifndef›			⇐ if_like‹**›
//	maybe	‹include›			⇐ if_like‹**›
//	maybe	‹inline›			⇐ int_like‹**›
//	maybe	‹int›				⇐ raw_int‹**›
//	maybe	‹jmp_buf›			⇐ raw_int‹**›
//	maybe	‹ldiv_t›			⇐ raw_int‹**›
//	maybe	‹line›				⇐ if_like‹**›
//	maybe	‹long›				⇐ raw_int‹**›
//	maybe	‹make_pair›			⇐ ftemplate‹\\{make\_pair}›
//	maybe	‹mutable›			⇐ int_like‹**›
//	maybe	‹namespace›			⇐ struct_like‹**›
//	maybe	‹new›				⇐ new_like‹**›
//	yes	‹not›				⇐ alfop‹**›
//	yes	‹not_eq›			⇐ alfop‹**›
//	yes	‹NULL›				⇐ exp‹\NULL›
//	maybe	‹offsetof›			⇐ raw_int‹**›
//	maybe	‹operator›			⇐ operator_like‹**›
//	yes	‹or›				⇐ alfop‹**›
//	yes	‹or_eq›				⇐ alfop‹**›
//	maybe	‹pragma›			⇐ if_like‹**›
//	maybe	‹private›			⇐ public_like‹**›
//	maybe	‹protected›			⇐ public_like‹**›
//	maybe	‹ptrdiff_t›			⇐ raw_int‹**›
//	maybe	‹public›			⇐ public_like‹**›
//	maybe	‹register›			⇐ int_like‹**›
//	maybe	‹reinterpret_cast›		⇐ raw_int‹**›
//	maybe	‹return›			⇐ case_like‹**›
//	maybe	‹short›				⇐ raw_int‹**›
//	maybe	‹sig_atomic_t›			⇐ raw_int‹**›
//	maybe	‹signed›			⇐ raw_int‹**›
//	maybe	‹size_t›			⇐ raw_int‹**›
//	maybe	‹sizeof›			⇐ sizeof_like‹**›
//	maybe	‹static›			⇐ int_like‹**›
//	maybe	‹static_cast›			⇐ raw_int‹**›
//	maybe	‹struct›			⇐ struct_like‹**›
//	maybe	‹switch›			⇐ for_like‹**›
//	maybe	‹template›			⇐ template_like‹**›
//	yes	‹TeX›				⇐ exp‹\TeX›
//	yes	‹this›				⇐ exp‹\this›
//	maybe	‹throw›				⇐ case_like‹**›
//	maybe	‹time_t›			⇐ raw_int‹**›
//	maybe	‹try›				⇐ else_like‹**›
//	maybe	‹typedef›			⇐ typedef_like‹**›
//	maybe	‹typeid›			⇐ raw_int‹**›
//	maybe	‹typename›			⇐ struct_like‹**›
//	maybe	‹undef›				⇐ if_like‹**›
//	maybe	‹union›				⇐ struct_like‹**›
//	maybe	‹unsigned›			⇐ raw_int‹**›
//	maybe	‹using›				⇐ int_like‹**›
//	maybe	‹va_dcl›			⇐ decl‹**›
//	maybe	‹va_list›			⇐ raw_int‹**›
//	maybe	‹virtual›			⇐ int_like‹**›
//	maybe	‹void›				⇐ raw_int‹**›
//	maybe	‹volatile›			⇐ const_like‹**›
//	maybe	‹wchar_t›			⇐ raw_int‹**›
//	maybe	‹while›				⇐ for_like‹**›
//	yes	‹xor›				⇐ alfop‹**›
//	yes	‹xor_eq›			⇐ alfop‹**›
//	maybe	‹@,›				⇐ insert‹\,›
//	maybe	‹@|›				⇐ insert‹≪opt≫ ‹0››
//	no	‹@/›				⇐ insert‹≪force≫›
//	no	‹@\#›				⇐ insert‹≪big_force≫›
//	no	‹@+›				⇐ insert‹≪big_cancel≫ ‹{}› ≪break_space≫ ‹{}› ≪big_cancel≫›
//	maybe	‹@;›				⇐ semi‹›
//	maybe	‹@[/*]*/›			⇐ begin_arg‹›
//	maybe	‹/*[*/@]›			⇐ end_arg‹›
//	maybe	‹@&›				⇐ insert‹\J›
//	no	‹@h›				⇐ insert‹≪force≫ ‹\ATH› ≪force≫›
//	maybe	‹@<› section name ‹@>›		⇐ section_scrap‹‹\X›n‹:›translated section name‹\X››
//	maybe	‹@(/*)*/› section name ‹@>›	⇐ section_scrap‹‹\X›n‹:\.{›section name with special characters quoted‹ }\X››
//	no	‹/*›comment‹*/›			⇐ insert‹≪cancel≫ ‹\C{›translated comment‹}› ≪force≫›
//	no	‹//›comment			⇐ insert‹≪cancel≫ ‹\SHC{›translated comment‹}› ≪force≫›
// The construction ‹@t› stuff ‹@>› contributes ‹\hbox{› stuff ‹}› to the following scrap.

#include "Prod.w"
// 3.0.6†

// ‡3.1. Implementing the Productions
// †3.1.4:
// Token lists in ≪†tok_mem≫ are composed of the following kinds of items for ‹TeX› output.
// ∙	Character codes and special codes like ≪force≫ and ≪math_rel≫ represent themselves;
// ∙	≪id_flag + p≫ represents ‹\\{identifier p}›;
// ∙	≪res_flag + p≫ represents ‹\&{identifier p}›;
// ∙	≪section_flag + p≫ represents section name ≪p≫;
// ∙	≪tok_flag + p≫ represents token list number ≪p≫;
// ∙	≪inner_tok_flag + p≫ represents token list number ≪p≫, to be translated without line-break controls.
#define id_flag 0x2800			// signifies an identifier
#define res_flag 2*id_flag		// signifies a reserved word
#define section_flag 3*id_flag		// signifies a section name
#define tok_flag 4*id_flag		// signifies a token list
#define inner_tok_flag 5*id_flag	// signifies a token list in ‛‹pb›’

void print_text(text_pointer p) {	// prints a token list for debugging; not used in ≪main≫
   if (p ≥ text_ptr) printf("BAD");
   else for (token_pointer j = *p; j < *(p + 1); j↑) {	// j: index into ≪tok_mem≫
      sixteen_bits r = *j%id_flag;	// remainder of token after the flag has been stripped off
      switch (*j/id_flag) {
      // ≪id_flag≫
         case 1: printf("\\\\{"/*}*/), print_id(name_dir + r), printf(/*{*/"}"); break;
      // ≪res_flag≫
         case 2: printf("\«"/*»*/), print_id(name_dir + r), printf(/*{*/"}"); break;
      // ≪section_flag≫
         case 3: printf("<"), print_section_name(name_dir + r), printf(">"); break;
      // ≪tok_flag≫
         case 4: printf("[[%d]]", r); break;
      // ≪inner_tok_flag≫
         case 5: printf("≪[[%d]]≫", r); break;
         default:
         // †3.1.5: Print token ≪r≫ in symbolic form
            switch (r) {
               case math_rel: printf("\\mathrel{"/*}*/); break;
               case big_cancel: printf("[ccancel]"); break;
               case cancel: printf("[cancel]"); break;
               case indent: printf("[indent]"); break;
               case outdent: printf("[outdent]"); break;
               case backup: printf("[backup]"); break;
               case opt: printf("[opt]"); break;
               case break_space: printf("[break]"); break;
               case force: printf("[force]"); break;
               case big_force: printf("[fforce]"); break;
               case preproc_line: printf("[preproc]"); break;
               case quoted_char: j↑, printf("[%o]", (unsigned)*j); break;
               case end_translation: printf("[quit]"); break;
               case inserted: printf("[inserted]"); break;
               default: putxchar(r);
            }
         // 3.1.5†
         break;
      }
   }
   fflush(stdout);
}

// 3.1.4†3.1.7:
void app_str(char *s) {
   while (*s ≠ '\0') app_tok(*s↑);
}

void big_app(token a) {
   if (a ≡ ' ' ∨ a ≥ big_cancel ∧ a ≤ big_force) {	// non-math token
      if (cur_mathness ≡ maybe_math) init_mathness = no_math;
      else if (cur_mathness ≡ yes_math) app_str("{}$");
      cur_mathness = no_math;
   } else {
      if (cur_mathness ≡ maybe_math) init_mathness = yes_math;
      else if (cur_mathness ≡ no_math) app_str("${}");
      cur_mathness = yes_math;
   }
   app(a);
}

void big_app1(scrap_pointer a) {
   switch (a→mathness%4) {	// left boundary
      case no_math:
         if (cur_mathness ≡ maybe_math) init_mathness = no_math;
         else if (cur_mathness ≡ yes_math) app_str("{}$");
         cur_mathness = a→mathness/4;	// right boundary
      break;
      case yes_math:
         if (cur_mathness ≡ maybe_math) init_mathness = yes_math;
         else if (cur_mathness ≡ no_math) app_str("${}");
         cur_mathness = a→mathness/4;	// right boundary
      break;
      case maybe_math: break;	// no changes
   }
   app(tok_flag + (int)((a)→trans - tok_start));
}

// 3.1.7†3.1.9:
// In ‹C99›, new specifier names can be defined via ≪typedef≫, and we want to make the parser recognize future occurrences of the identifier thus defined as specifiers.
// This is done by the procedure ≪make_reserved≫, which changes the ≪ilk≫ of the relevant identifier.

// We first need a procedure to recursively seek the first identifier in a token list,
// because the identifier might be enclosed in parentheses, as when one defines a function returning a pointer.

// If the first identifier found is a keyword like ‛«case»’, we return the special value ≪case_found≫;
// this prevents underlining of identifiers in case labels.

// If the first identifier is the keyword ‛«operator»’, we give up;
// users who want to index definitions of overloaded ‹C++› operators should say, for example, ‛≪@!@^\&{operator} $+{=}$@>≫’
// (or, more properly alphebetized, ‛‹@!@:operator+=›{\&{operator} $+{=}$@>}’).
#define no_ident_found (token_pointer)0	// distinct from any identifier token
#define case_found (token_pointer)1	// likewise
#define operator_found (token_pointer)2	// likewise

token_pointer find_first_ident(text_pointer p) {
   if (p ≥ text_ptr) confusion("find_first_ident");
   for (token_pointer j = *p; j < *(p + 1); j↑) {	// j: token being looked at
      sixteen_bits r = *j%id_flag;	// remainder of token after the flag has been stripped off
      switch (*j/id_flag) {
         case 2:	// ≪res_flag≫
            if (name_dir[r].ilk ≡ case_like) return case_found;
            if (name_dir[r].ilk ≡ operator_like) return operator_found;
            if (name_dir[r].ilk ≠ raw_int) break;
         case 1:
         return j;
         case 4: case 5: {	// ≪tok_flag≫ or ≪inner_tok_flag≫
            token_pointer q = find_first_ident(tok_start + r);	// token to be returned
            if (q ≠ no_ident_found) return q;
         }
         default:	// char, ≪section_flag≫, fall thru: move on to next token
            if (*j ≡ inserted) return no_ident_found;	// ignore inserts
            else if (*j ≡ qualifier) j↑;	// bypass namespace qualifier
         break;
      }
   }
   return no_ident_found;
}

// 3.1.9†3.1.10:
// The scraps currently being parsed must be inspected for any occurrence of the identifier that we're making reserved; hence the ≪for≫ loop below.
void make_reserved(scrap_pointer p) {	// make the first identifier in ≪p→trans≫ like ≪int≫
   token_pointer tok_loc = find_first_ident(p→trans);	// pointer to ≪tok_value≫
   if (tok_loc ≤ operator_found) return;	// this should not happen
   sixteen_bits tok_value = *tok_loc;	// the name of this identifier, plus its flag
   for (; p ≤ scrap_ptr; p ≡ lo_ptr? p = hi_ptr: p↑) if (p→cat ≡ exp ∧ **p→trans ≡ tok_value) p→cat = raw_int, **p→trans = tok_value%id_flag + res_flag;
   (name_dir + (sixteen_bits)(tok_value%id_flag))→ilk = raw_int, *tok_loc = tok_value%id_flag + res_flag;
}

// 3.1.10†3.1.11:
// In the following situations we want to mark the occurrence of an identifier as a definition: when ≪make_reserved≫ is just about to be used;
// after a specifier, as in ≪char **argv≫; before a colon, as in «·found·»:; and in the declaration of a function, as in «·main·»(){ …; }.
// This is accomplished by the invocation of ≪make_underlined≫ at appropriate times.
// Notice that, in the declaration of a function, we find out that the identifier is being defined only after it has been swallowed up by an ≪exp≫.
void make_underlined(scrap_pointer p) {	// underline the entry for the first identifier in ≪p→trans≫
   token_pointer tok_loc = find_first_ident(p→trans);	// where the first identifier appears
   if (tok_loc ≤ operator_found) return;	// this happens, for example, in ≪case found:≫
   xref_switch = def_flag, underline_xref(*tok_loc%id_flag + name_dir);
}

// 3.1.11†3.1.13:
void underline_xref(name_pointer p) {
   if (no_xref) return;
   xref_pointer q = (xref_pointer)p→xref;	// pointer to cross-reference being examined
   sixteen_bits m = section_count + xref_switch;	// cross-reference value to be installed
   for (; q ≠ xmem; q = q→xlink) {
      sixteen_bits n = q→num;	// cross-reference value being examined
      if (n ≡ m) return;
      else if (m ≡ n + def_flag) { q→num = m; return; }
      else if (n ≥ def_flag ∧ n < m) break;
   }
// †3.1.14: Insert new cross-reference at ≪q≫, not at beginning of list
// We get to this section only when the identifier is one letter long, so it didn't get a non-underlined entry during phase one.
// But it may have got some explicitly underlined entries in later sections, so in order to preserve the numerical order of the entries in the index,
// we have to insert the new cross-reference not at the beginning of the list (namely, at ≪p→xref≫), but rather right before ≪q≫.
   append_xref(0);	// this number doesn't matter
   xref_ptr→xlink = (xref_pointer)p→xref;
   xref_pointer r = xref_ptr;	// temporary pointer for permuting cross-references
   p→xref = (char *)xref_ptr;
   for (; r→xlink ≠ q; r = r→xlink) r→num = r→xlink→num;
   r→num = m;	// everything from ≪q≫ on is left undisturbed
// 3.1.14†
}

// 3.1.13†3.1.62:
// Now here's the ≪reduce≫ procedure used in our code for productions.

// The ‛≪freeze_text()≫’ macro is used to give official status to a token list.
// Before saying ≪freeze_text()≫, items are appended to the current token list,
// and we know that the eventual number of this token list will be the current value of ≪text_ptr≫.
// But no list of that number really exists as yet, because no ending point for the current list has been stored in the ≪tok_start≫ array.
// After saying ≪freeze_text()≫, the old current token list becomes legitimate,
// and its number is the current value of ≪text_ptr - 1≫ since ≪text_ptr≫ has been increased.
// The new current token list is empty and ready to be appended to.
// Note that ≪freeze_text()≫ does not check to see that ≪text_ptr≫ hasn't gotten too large, since it is assumed that this test was done beforehand.

#define freeze_text() *↑text_ptr = tok_ptr

void reduce(scrap_pointer j, short k, eight_bits c, short d, short n) {
   j→cat = c, j→trans = text_ptr, j→mathness = 4*cur_mathness + init_mathness;
   freeze_text();
   if (k > 1) {
      for (scrap_pointer i = j + k, i1 = j + 1; i ≤ lo_ptr; i↑, i1↑) i1→cat = i→cat, i1→trans = i→trans, i1→mathness = i→mathness;
      lo_ptr -= k - 1;
   }
   pp = (pp + d < scrap_base? scrap_base: pp + d);
   PrintSnapShot(n);	// Print a snapshot of the scrap list if debugging≫≫
   pp↓;	// we next say ≪pp↑≫
}

// 3.1.62†3.1.63:
// Here's the ≪squash≫ procedure, which takes advantage of the simplification that occurs when ≪k ≡ 1≫.
void squash(scrap_pointer j, short k, eight_bits c, short d, short n) {
   if (k ≡ 1) {
      j→cat = c; pp = (pp + d < scrap_base? scrap_base: pp + d);
      PrintSnapShot(n);	// Print a snapshot of the scrap list if debugging≫≫
      pp↓;	// we next say ≪pp↑≫
   } else {
      for (scrap_pointer i = j; i < j + k; i↑) big_app1(i);
      reduce(j, k, c, d, n);
   }
}
// 3.1.63†

// †3.1.67: [2] Print a snapshot of the scrap list if debugging
// Editor's Note:
// ∙	This was orginally a multiply-used module.
inline void PrintSnapShot(short n) {
   if (tracing ≡ 2) {
      printf("\n%d:", n);
      for (scrap_pointer k = scrap_base; k ≤ lo_ptr; k↑) {
         putxchar(k ≡ pp? '*': ' ');
         if (k→mathness%4 ≡ yes_math) putchar('+');
         else if (k→mathness%4 ≡ no_math) putchar('-');
         print_cat(k→cat);
         if (k→mathness/4 ≡ yes_math) putchar('+');
         else if (k→mathness/4 ≡ no_math) putchar('-');
      }
      if (hi_ptr ≤ scrap_ptr) printf("...");	// indicate that more is coming
   }
}

// 3.1.67†3.1.68:
// The ≪translate≫ function assumes that scraps have been stored in positions ≪scrap_base≫ through ≪scrap_ptr≫ of ≪cat≫ and ≪trans≫.
// It applies productions as much as possible.
// The result is a token list containing the translation of the given sequence of scraps.

// After calling ≪translate≫, we will have ≪text_ptr + 3 ≤ max_texts≫ and ≪tok_ptr + 6 ≤ max_toks≫,
// so it will be possible to create up to three token lists with up to six tokens without checking for overflow.
// Before calling ≪translate≫, we should have ≪text_ptr < max_texts≫ and ≪scrap_ptr < max_scraps≫,
// since ≪translate≫ might add a new text and a new scrap before it checks for overflow.
text_pointer translate(void) {	// converts a sequence of scraps
   pp = scrap_base, lo_ptr = pp - 1, hi_ptr = pp;
// †3.1.71: If tracing, print an indication of where we are
   if (tracing ≡ 2) {
      printf("\nTracing after l. %d:\n", cur_line), mark_harmless();	// ⁅039⁆
      if (loc > buffer + 50) printf("..."), term_write(loc - 51, 51);
      else term_write(buffer, loc - buffer);
   }
// 3.1.71†3.1.64: Reduce the scraps using the productions until no more rules apply
// And here now is the code that applies productions as long as possible.
// Before applying the production mechanism, we must make sure it has good input (at least four scraps, the length of the lhs of the longest rules),
// and that there is enough room in the memory arrays to hold the appended tokens and texts.
// Here we use a very conservative test;
// it's more important to make sure the program will still work if we change the production rules (within reason)
// than to squeeze the last bit of space from the memory arrays.
#define safe_tok_incr 20
#define safe_text_incr 10
#define safe_scrap_incr 10
   while (1) {
   // †3.1.65: Make sure the entries ≪pp≫ through ≪pp + 3≫ of ≪cat≫ are defined
   // If we get to the end of the scrap list, category codes equal to zero are stored, since zero does not match anything in a production.
      if (lo_ptr < pp + 3) {
         while (hi_ptr ≤ scrap_ptr ∧ lo_ptr ≠ pp + 3)
            (↑lo_ptr)→cat = hi_ptr→cat, lo_ptr→mathness = hi_ptr→mathness, lo_ptr→trans = (hi_ptr↑)→trans;
         for (scrap_pointer i = lo_ptr + 1; i ≤ pp + 3; i↑) i→cat = 0;
      }
   // 3.1.65†
      if (tok_ptr + safe_tok_incr > tok_mem_end) {
         if (tok_ptr > max_tok_ptr) max_tok_ptr = tok_ptr;
         overflow("token");
      }
      if (text_ptr + safe_text_incr > tok_start_end) {
         if (text_ptr > max_text_ptr) max_text_ptr = text_ptr;
         overflow("text");
      }
      if (pp > lo_ptr) break;
      init_mathness = cur_mathness = maybe_math;
   // †3.1.8: Match a production at ≪pp≫, or increase ≪pp≫ if there is no match
   // Let us consider the big switch for productions now, before looking at its context.
   // We want to design the program so that this switch works,
   // so we might as well not keep ourselves in suspense about exactly what code needs to be provided with a proper environment.
   #define cat1 (pp + 1)→cat
   #define cat2 (pp + 2)→cat
   #define cat3 (pp + 3)→cat
   #define lhs_not_simple (pp→cat ≠ public_like ∧ pp→cat ≠ semi ∧ pp→cat ≠ prelangle ∧ pp→cat ≠ prerangle ∧ pp→cat ≠ template_like ∧ pp→cat ≠ new_like ∧ pp→cat ≠ new_exp ∧ pp→cat ≠ ftemplate ∧ pp→cat ≠ raw_ubin ∧ pp→cat ≠ const_like ∧ pp→cat ≠ raw_int ∧ pp→cat ≠ operator_like)	// not a production with left side length 1
      if (cat1 ≡ end_arg ∧ lhs_not_simple)
         if (pp→cat ≡ begin_arg) squash(pp, 2, exp, -2, 124);
         else squash(pp, 2, end_arg, -1, 125);
      else if (cat1 ≡ insert) squash(pp, 2, pp→cat, -2, 0);
      else if (cat2 ≡ insert) squash(pp + 1, 2, (pp + 1)→cat, -1, 0);
      else if (cat3 ≡ insert) squash(pp + 2, 2, (pp + 2)→cat, 0, 0);
      else
      switch (pp→cat) {
         case exp:
         // †3.1.15: Cases for ≪exp≫
         // Now comes the code that tries to match each production starting with a particular type of scrap.
         // Whenever a match is discovered, the ≪squash≫ or ≪reduce≫ macro will cause the appropriate action to be performed, followed by ≪goto found≫.
            if (cat1 ≡ lbrace ∨ cat1 ≡ int_like ∨ cat1 ≡ decl) make_underlined(pp), big_app1(pp), big_app(indent), app(indent), reduce(pp, 1, fn_decl, 0, 1);
            else if (cat1 ≡ unop) squash(pp, 2, exp, -2, 2);
            else if ((cat1 ≡ binop ∨ cat1 ≡ ubinop) ∧ cat2 ≡ exp) squash(pp, 3, exp, -2, 3);
            else if (cat1 ≡ comma ∧ cat2 ≡ exp) big_app2(pp), app(opt), app('9'), big_app1(pp + 2), reduce(pp, 3, exp, -2, 4);
            else if (cat1 ≡ lpar ∧ cat2 ≡ rpar ∧ cat3 ≡ colon) squash(pp + 3, 1, base, 0, 5);
            else if (cat1 ≡ cast ∧ cat2 ≡ colon) squash(pp + 2, 1, base, 0, 5);
            else if (cat1 ≡ semi) squash(pp, 2, stmt, -1, 6);
            else if (cat1 ≡ colon) make_underlined(pp), squash(pp, 2, tag, -1, 7);
            else if (cat1 ≡ rbrace) squash(pp, 1, stmt, -1, 8);
            else if (cat1 ≡ lpar ∧ cat2 ≡ rpar ∧ (cat3 ≡ const_like ∨ cat3 ≡ case_like)) big_app1(pp + 2), big_app(' '), big_app1(pp + 3), reduce(pp + 2, 2, rpar, 0, 9);
            else if (cat1 ≡ cast ∧ (cat2 ≡ const_like ∨ cat2 ≡ case_like)) big_app1(pp + 1), big_app(' '), big_app1(pp + 2), reduce(pp + 1, 2, cast, 0, 9);
            else if (cat1 ≡ exp ∨ cat1 ≡ cast) squash(pp, 2, exp, -2, 10);
         // 3.1.15†
         break;
         case lpar:
         // †3.1.16: Cases for ≪lpar≫
            if ((cat1 ≡ exp ∨ cat1 ≡ ubinop) ∧ cat2 ≡ rpar) squash(pp, 3, exp, -2, 11);
            else if (cat1 ≡ rpar) big_app1(pp), app('\\'), app(','), big_app1(pp + 1), reduce(pp, 2, exp, -2, 12);	// ⁅040⁆
            else if ((cat1 ≡ decl_head ∨ cat1 ≡ int_like ∨ cat1 ≡ cast) ∧ cat2 ≡ rpar) squash(pp, 3, cast, -2, 13);
            else if ((cat1 ≡ decl_head ∨ cat1 ≡ int_like ∨ cat1 ≡ exp) ∧ cat2 ≡ comma) big_app3(pp), app(opt), app('9'), reduce(pp, 3, lpar, -1, 14);
            else if (cat1 ≡ stmt ∨ cat1 ≡ decl) big_app2(pp), big_app(' '), reduce(pp, 2, lpar, -1, 15);
         // 3.1.16†
         break;
         case unop:
         // †3.1.17: Cases for ≪unop≫
            if (cat1 ≡ exp ∨ cat1 ≡ int_like) squash(pp, 2, exp, -2, 16);
         // 3.1.17†
         break;
         case ubinop:
         // †3.1.18: Cases for ≪ubinop≫
            if (cat1 ≡ cast ∧ cat2 ≡ rpar) big_app('{'), big_app1(pp), big_app('}'), big_app1(pp + 1), reduce(pp, 2, cast, -2, 17);
            else if (cat1 ≡ exp ∨ cat1 ≡ int_like) big_app('{'), big_app1(pp), big_app('}'), big_app1(pp + 1), reduce(pp, 2, cat1, -2, 18);
            else if (cat1 ≡ binop) big_app(math_rel), big_app1(pp), big_app('{'), big_app1(pp + 1), big_app('}'), big_app('}'), reduce(pp, 2, binop, -1, 19);
         // 3.1.18†
         break;
         case binop:
         // †3.1.19: Cases for ≪binop≫
            if (cat1 ≡ binop)
               big_app(math_rel), big_app('{'), big_app1(pp), big_app('}'), big_app('{'), big_app1(pp + 1), big_app('}'), big_app('}'), reduce(pp, 2, binop, -1, 20);
         // 3.1.19†
         break;
         case cast:
         // †3.1.20: Cases for ≪cast≫
            if (cat1 ≡ lpar) squash(pp, 2, lpar, -1, 21);
            else if (cat1 ≡ exp) big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, exp, -2, 21);
            else if (cat1 ≡ semi) squash(pp, 1, exp, -2, 22);
         // 3.1.20†
         break;
         case sizeof_like:
         // †3.1.21: Cases for ≪sizeof_like≫
            if (cat1 ≡ cast) squash(pp, 2, exp, -2, 23);
            else if (cat1 ≡ exp) big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, exp, -2, 24);
         // 3.1.21†
         break;
         case int_like:
         // †3.1.22: Cases for ≪int_like≫
            if (cat1 ≡ int_like ∨ cat1 ≡ struct_like) big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, cat1, -2, 25);
            else if (cat1 ≡ exp ∧ (cat2 ≡ raw_int ∨ cat2 ≡ struct_like)) squash(pp, 2, int_like, -2, 26);
            else if (cat1 ≡ exp ∨ cat1 ≡ ubinop ∨ cat1 ≡ colon) big_app1(pp), big_app(' '), reduce(pp, 1, decl_head, -1, 27);
            else if (cat1 ≡ semi ∨ cat1 ≡ binop) squash(pp, 1, decl_head, 0, 28);
         // 3.1.22†
         break;
         case public_like:
         // †3.1.23: Cases for ≪public_like≫
            if (cat1 ≡ colon) squash(pp, 2, tag, -1, 29);
            else squash(pp, 1, int_like, -2, 30);
         // 3.1.23†
         break;
         case colcol:
         // †3.1.24: Cases for ≪colcol≫
            if (cat1 ≡ exp ∨ cat1 ≡ int_like) app(qualifier), squash(pp, 2, cat1, -2, 31);
            else if (cat1 ≡ colcol) squash(pp, 2, colcol, -1, 32);
         // 3.1.24†
         break;
         case decl_head:
         // †3.1.25: Cases for ≪decl_head≫
            if (cat1 ≡ comma) big_app2(pp), big_app(' '), reduce(pp, 2, decl_head, -1, 33);
            else if (cat1 ≡ ubinop) big_app1(pp), big_app('{'), big_app1(pp + 1), big_app('}'), reduce(pp, 2, decl_head, -1, 34);
            else if (cat1 ≡ exp ∧ cat2 ≠ lpar ∧ cat2 ≠ exp ∧ cat2 ≠ cast) make_underlined(pp + 1), squash(pp, 2, decl_head, -1, 35);
            else if ((cat1 ≡ binop ∨ cat1 ≡ colon) ∧ cat2 ≡ exp ∧ (cat3 ≡ comma ∨ cat3 ≡ semi ∨ cat3 ≡ rpar)) squash(pp, 3, decl_head, -1, 36);
            else if (cat1 ≡ cast) squash(pp, 2, decl_head, -1, 37);
            else if (cat1 ≡ lbrace ∨ cat1 ≡ int_like ∨ cat1 ≡ decl) big_app1(pp), big_app(indent), app(indent), reduce(pp, 1, fn_decl, 0, 38);
            else if (cat1 ≡ semi) squash(pp, 2, decl, -1, 39);
         // 3.1.25†
         break;
         case decl:
         // †3.1.26: Cases for ≪decl≫
            if (cat1 ≡ decl) big_app1(pp), big_app(force), big_app1(pp + 1), reduce(pp, 2, decl, -1, 40);
            else if (cat1 ≡ stmt ∨ cat1 ≡ function) big_app1(pp), big_app(big_force), big_app1(pp + 1), reduce(pp, 2, cat1, -1, 41);
         // 3.1.26†
         break;
         case base:
         // †3.1.27: Cases for ≪base≫
            if (cat1 ≡ int_like ∨ cat1 ≡ exp) {
               if (cat2 ≡ comma) big_app1(pp), big_app(' '), big_app2(pp + 1), app(opt), app('9'), reduce(pp, 3, base, 0, 42);
               else if (cat2 ≡ lbrace) big_app1(pp), big_app(' '), big_app1(pp + 1), big_app(' '), big_app1(pp + 2), reduce(pp, 3, lbrace, -2, 43);
            }
         // 3.1.27†
         break;
         case struct_like:
         // †3.1.28: Cases for ≪struct_like≫
            if (cat1 ≡ lbrace) big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, struct_head, 0, 44);
            else if (cat1 ≡ exp ∨ cat1 ≡ int_like) {
               if (cat2 ≡ lbrace ∨ cat2 ≡ semi) {
                  make_underlined(pp + 1), make_reserved(pp + 1), big_app1(pp), big_app(' '), big_app1(pp + 1);
                  if (cat2 ≡ semi) reduce(pp, 2, decl_head, 0, 45);
                  else big_app(' '), big_app1(pp + 2), reduce(pp, 3, struct_head, 0, 46);
               } else if (cat2 ≡ colon) squash(pp + 2, 1, base, 2, 47);
               else if (cat2 ≠ base) big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, int_like, -2, 48);
            }
         // 3.1.28†
         break;
         case struct_head:
         // †3.1.29: Cases for ≪struct_head≫
            if ((cat1 ≡ decl ∨ cat1 ≡ stmt ∨ cat1 ≡ function) ∧ cat2 ≡ rbrace)
               big_app1(pp), big_app(indent), big_app(force), big_app1(pp + 1), big_app(outdent), big_app(force), big_app1(pp + 2), reduce(pp, 3, int_like, -2, 49);
            else if (cat1 ≡ rbrace)
               big_app1(pp), app_str("\\,"), big_app1(pp + 1), reduce(pp, 2, int_like, -2, 50);	// ⁅041⁆
         // 3.1.29†
         break;
         case fn_decl:
         // †3.1.30: Cases for ≪fn_decl≫
            if (cat1 ≡ decl) big_app1(pp), big_app(force), big_app1(pp + 1), reduce(pp, 2, fn_decl, 0, 51);
            else if (cat1 ≡ stmt) big_app1(pp), app(outdent), app(outdent), big_app(force), big_app1(pp + 1), reduce(pp, 2, function, -1, 52);
         // 3.1.30†
         break;
         case function:
         // †3.1.31: Cases for ≪function≫
            if (cat1 ≡ function ∨ cat1 ≡ decl ∨ cat1 ≡ stmt) big_app1(pp), big_app(big_force), big_app1(pp + 1), reduce(pp, 2, cat1, -1, 53);
         // 3.1.31†
         break;
         case lbrace:
         // †3.1.32: Cases for ≪lbrace≫
            if (cat1 ≡ rbrace) big_app1(pp), app('\\'), app(','), big_app1(pp + 1), reduce(pp, 2, stmt, -1, 54);	// ⁅042⁆
            else if ((cat1 ≡ stmt ∨ cat1 ≡ decl ∨ cat1 ≡ function) ∧ cat2 ≡ rbrace)
               big_app(force), big_app1(pp), big_app(indent), big_app(force),
               big_app1(pp + 1), big_app(force), big_app(backup), big_app1(pp + 2),
               big_app(outdent), big_app(force), reduce(pp, 3, stmt, -1, 55);
            else if (cat1 ≡ exp) {
               if (cat2 ≡ rbrace) squash(pp, 3, exp, -2, 56);
               else if (cat2 ≡ comma ∧ cat3 ≡ rbrace) squash(pp, 4, exp, -2, 56);
            }
         // 3.1.32†
         break;
         case if_like:
         // †3.1.33: Cases for ≪if_like≫
            if (cat1 ≡ exp) big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, if_clause, 0, 57);
         // 3.1.33†
         break;
         case else_like:
         // †3.1.34: Cases for ≪else_like≫
            if (cat1 ≡ colon) squash(pp + 1, 1, base, 1, 58);
            else if (cat1 ≡ lbrace) squash(pp, 1, else_head, 0, 59);
            else if (cat1 ≡ stmt)
               big_app(force), big_app1(pp), big_app(indent), big_app(break_space),
               big_app1(pp + 1), big_app(outdent), big_app(force),
               reduce(pp, 2, stmt, -1, 60);
         // 3.1.34†
         break;
         case else_head:
         // †3.1.35: Cases for ≪else_head≫
            if (cat1 ≡ stmt ∨ cat1 ≡ exp)
               big_app(force), big_app1(pp), big_app(break_space), app(noop),
               big_app(cancel), big_app1(pp + 1), big_app(force), reduce(pp, 2, stmt, -1, 61);
         // 3.1.35†
         break;
         case if_clause:
         // †3.1.36: Cases for ≪if_clause≫
            if (cat1 ≡ lbrace) squash(pp, 1, if_head, 0, 62);
            else if (cat1 ≡ stmt) {
               if (cat2 ≡ else_like) {
                  big_app(force), big_app1(pp), big_app(indent), big_app(break_space),
                  big_app1(pp + 1), big_app(outdent), big_app(force), big_app1(pp + 2);
                  if (cat3 ≡ if_like) big_app(' '), big_app1(pp + 3), reduce(pp, 4, if_like, 0, 63);
                  else reduce(pp, 3, else_like, 0, 64);
               } else squash(pp, 1, else_like, 0, 65);
            }
         // 3.1.36†
         break;
         case if_head:
         // †3.1.37: Cases for ≪if_head≫
            if (cat1 ≡ stmt ∨ cat1 ≡ exp) {
               if (cat2 ≡ else_like) {
                  big_app(force), big_app1(pp), big_app(break_space), app(noop),
                  big_app(cancel), big_app1(pp + 1), big_app(force), big_app1(pp + 2);
                  if (cat3 ≡ if_like) big_app(' '), big_app1(pp + 3), reduce(pp, 4, if_like, 0, 66);
                  else reduce(pp, 3, else_like, 0, 67);
               } else squash(pp, 1, else_head, 0, 68);
            }
         // 3.1.37†
         break;
         case do_like:
         // †3.1.38: Cases for ≪do_like≫
            if (cat1 ≡ stmt ∧ cat2 ≡ else_like ∧ cat3 ≡ semi)
               big_app1(pp), big_app(break_space), app(noop), big_app(cancel),
               big_app1(pp + 1), big_app(cancel), app(noop), big_app(break_space),
               big_app2(pp + 2), reduce(pp, 4, stmt, -1, 69);
         // 3.1.38†
         break;
         case case_like:
         // †3.1.39: Cases for ≪case_like≫
            if (cat1 ≡ semi) squash(pp, 2, stmt, -1, 70);
            else if (cat1 ≡ colon) squash(pp, 2, tag, -1, 71);
            else if (cat1 ≡ exp) big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, exp, -2, 72);
         // 3.1.39†
         break;
         case catch_like:
         // †3.1.40: Cases for ≪catch_like≫
            if (cat1 ≡ cast ∨ cat1 ≡ exp) big_app2(pp), big_app(indent), big_app(indent), reduce(pp, 2, fn_decl, 0, 73);
         // 3.1.40†
         break;
         case tag:
         // †3.1.41: Cases for ≪tag≫
            if (cat1 ≡ tag) big_app1(pp), big_app(break_space), big_app1(pp + 1), reduce(pp, 2, tag, -1, 74);
            else if (cat1 ≡ stmt ∨ cat1 ≡ decl ∨ cat1 ≡ function) big_app(force), big_app(backup), big_app1(pp), big_app(break_space), big_app1(pp + 1), reduce(pp, 2, cat1, -1, 75);
         // 3.1.41†
         break;
         case stmt:
         // †3.1.42: Cases for ≪stmt≫
         // The user can decide at run-time whether short statements should be grouped together on the same line.
#define force_lines flags['f']	// should each statement be on its own line?
            if (cat1 ≡ stmt ∨ cat1 ≡ decl ∨ cat1 ≡ function) {
               big_app1(pp);
               if (cat1 ≡ function) big_app(big_force);
               else if (cat1 ≡ decl) big_app(big_force);
               else if (force_lines) big_app(force);
               else big_app(break_space);
               big_app1(pp + 1), reduce(pp, 2, cat1, -1, 76);
            }
         // 3.1.42†
         break;
         case semi:
         // †3.1.43: Cases for ≪semi≫
            big_app(' '), big_app1(pp), reduce(pp, 1, stmt, -1, 77);
         // 3.1.43†
         break;
         case lproc:
         // †3.1.44: Cases for ≪lproc≫
            if (cat1 ≡ define_like) make_underlined(pp + 2);
            if (cat1 ≡ else_like ∨ cat1 ≡ if_like ∨ cat1 ≡ define_like) squash(pp, 2, lproc, 0, 78);
            else if (cat1 ≡ rproc) app(inserted), big_app2(pp), reduce(pp, 2, insert, -1, 79);
            else if (cat1 ≡ exp ∨ cat1 ≡ function) {
               if (cat2 ≡ rproc) app(inserted), big_app1(pp), big_app(' '), big_app2(pp + 1), reduce(pp, 3, insert, -1, 80);
               else if (cat2 ≡ exp ∧ cat3 ≡ rproc ∧ cat1 ≡ exp)
                  app(inserted), big_app1(pp), big_app(' '), big_app1(pp + 1), app_str(" \\5"),	// ⁅043⁆
                  big_app2(pp + 2), reduce(pp, 4, insert, -1, 80);
            }
         // 3.1.44†
         break;
         case section_scrap:
         // †3.1.45: Cases for ≪section_scrap≫
            if (cat1 ≡ semi) big_app2(pp), big_app(force), reduce(pp, 2, stmt, -2, 81);
            else squash(pp, 1, exp, -2, 82);
         // 3.1.45†
         break;
         case insert:
         // †3.1.46: Cases for ≪insert≫
            if (cat1) squash(pp, 2, cat1, 0, 83);
         // 3.1.46†
         break;
         case prelangle:
         // †3.1.47: Cases for ≪prelangle≫
            init_mathness = cur_mathness = yes_math, app('<'), reduce(pp, 1, binop, -2, 84);
         // 3.1.47†
         break;
         case prerangle:
         // †3.1.48: Cases for ≪prerangle≫
            init_mathness = cur_mathness = yes_math, app('>'), reduce(pp, 1, binop, -2, 85);
         // 3.1.48†
         break;
         case langle:
         // †3.1.49: Cases for ≪langle≫
            if (cat1 ≡ prerangle)
               big_app1(pp), app('\\'), app(','), big_app1(pp + 1),	// ⁅044⁆
               reduce(pp, 2, cast, -1, 86);
            else if (cat1 ≡ decl_head ∨ cat1 ≡ int_like ∨ cat1 ≡ exp) {
               if (cat2 ≡ prerangle) squash(pp, 3, cast, -1, 87);
               else if (cat2 ≡ comma) big_app3(pp), app(opt), app('9'), reduce(pp, 3, langle, 0, 88);
            }
         // 3.1.49†
         break;
         case template_like:
         // †3.1.50: Cases for ≪template_like≫
            if (cat1 ≡ exp ∧ cat2 ≡ prelangle) squash(pp + 2, 1, langle, 2, 89);
            else if (cat1 ≡ exp ∨ cat1 ≡ raw_int) big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, cat1, -2, 90);
            else squash(pp, 1, raw_int, 0, 91);
         // 3.1.50†
         break;
         case new_like:
         // †3.1.51: Cases for ≪new_like≫
            if (cat1 ≡ lpar ∧ cat2 ≡ exp ∧ cat3 ≡ rpar) squash(pp, 4, new_like, 0, 92);
            else if (cat1 ≡ cast) big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, exp, -2, 93);
            else if (cat1 ≠ lpar) squash(pp, 1, new_exp, 0, 94);
         // 3.1.51†
         break;
         case new_exp:
         // †3.1.52: Cases for ≪new_exp≫
            if (cat1 ≡ int_like ∨ cat1 ≡ const_like) big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, new_exp, 0, 95);
            else if (cat1 ≡ struct_like ∧ (cat2 ≡ exp ∨ cat2 ≡ int_like)) big_app1(pp), big_app(' '), big_app1(pp + 1), big_app(' '), big_app1(pp + 2), reduce(pp, 3, new_exp, 0, 96);
            else if (cat1 ≡ raw_ubin) big_app1(pp), big_app('{'), big_app1(pp + 1), big_app('}'), reduce(pp, 2, new_exp, 0, 97);
            else if (cat1 ≡ lpar) squash(pp, 1, exp, -2, 98);
            else if (cat1 ≡ exp) big_app1(pp), big_app(' '), reduce(pp, 1, exp, -2, 98);
            else if (cat1 ≠ raw_int ∧ cat1 ≠ struct_like ∧ cat1 ≠ colcol) squash(pp, 1, exp, -2, 99);
         // 3.1.52†
         break;
         case ftemplate:
         // †3.1.53: Cases for ≪ftemplate≫
            if (cat1 ≡ prelangle) squash(pp + 1, 1, langle, 1, 100);
            else squash(pp, 1, exp, -2, 101);
         // 3.1.53†
         break;
         case for_like:
         // †3.1.54: Cases for ≪for_like≫
            if (cat1 ≡ exp) big_app1(pp), big_app(' '), big_app1(pp+  1), reduce(pp, 2, else_like, -2, 102);
         // 3.1.54†
         break;
         case raw_ubin:
         // †3.1.55: Cases for ≪raw_ubin≫
            if (cat1 ≡ const_like) big_app2(pp), app_str("\\ "), reduce(pp, 2, raw_ubin, 0, 103);	// ⁅045⁆
            else squash(pp, 1, ubinop, -2, 104);
         // 3.1.55†
         break;
         case const_like:
         // †3.1.56: Cases for ≪const_like≫
            squash(pp, 1, int_like, -2, 105);
         // 3.1.56†
         break;
         case raw_int:
         // †3.1.57: Cases for ≪raw_int≫
            if (cat1 ≡ prelangle) squash(pp + 1, 1, langle, 1, 106);
            else if (cat1 ≡ colcol) squash(pp, 2, colcol, -1, 107);
            else if (cat1 ≡ cast) squash(pp, 2, raw_int, 0, 108);
            else if (cat1 ≡ lpar) squash(pp, 1, exp, -2, 109);
            else if (cat1 ≠ langle) squash(pp, 1, int_like, -3, 110);
         // 3.1.57†
         break;
         case operator_like:
         // †3.1.58: Cases for ≪operator_like≫
            if (cat1 ≡ binop ∨ cat1 ≡ unop ∨ cat1 ≡ ubinop) {
               if (cat2 ≡ binop) break;
               big_app1(pp), big_app('{'), big_app1(pp + 1), big_app('}'), reduce(pp, 2, exp, -2, 111);
            } else if (cat1 ≡ new_like ∨ cat1 ≡ delete_like) big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, exp, -2, 112);
            else if (cat1 ≡ comma) squash(pp, 2, exp, -2, 113);
            else if (cat1 ≠ raw_ubin) squash(pp, 1, new_exp, 0, 114);
         // 3.1.58†
         break;
         case typedef_like:
         // †3.1.59: Cases for ≪typedef_like≫
            if ((cat1 ≡ int_like ∨ cat1 ≡ cast) ∧ (cat2 ≡ comma ∨ cat2 ≡ semi)) squash(pp + 1, 1, exp, -1, 115);
            else if (cat1 ≡ int_like) big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, typedef_like, 0, 116);
            else if (cat1 ≡ exp ∧ cat2 ≠ lpar ∧ cat2 ≠ exp ∧ cat2 ≠ cast)
               make_underlined(pp + 1), make_reserved(pp + 1), big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, typedef_like, 0, 117);
            else if (cat1 ≡ comma) big_app2(pp), big_app(' '), reduce(pp, 2, typedef_like, 0, 118);
            else if (cat1 ≡ semi) squash(pp, 2, decl, -1, 119);
            else if (cat1 ≡ ubinop ∧ (cat2 ≡ ubinop ∨ cat2 ≡ cast))
               big_app('{'), big_app1(pp + 1), big_app('}'), big_app1(pp + 2), reduce(pp + 1, 2, cat2, 0, 120);
         // 3.1.59†
         break;
         case delete_like:
         // †3.1.60: Cases for ≪delete_like≫
            if (cat1 ≡ lpar ∧ cat2 ≡ rpar) big_app2(pp), app('\\'), app(','), big_app1(pp + 2), reduce(pp, 3, delete_like, 0, 121);	// ⁅046⁆
            else if (cat1 ≡ exp) big_app1(pp), big_app(' '), big_app1(pp + 1), reduce(pp, 2, exp, -2, 122);
         // 3.1.60†
         break;
         case question:
         // †3.1.61: Cases for ≪question≫
            if (cat1 ≡ exp ∧ (cat2 ≡ colon ∨ cat2 ≡ base))
               (pp + 2)→mathness = 5*yes_math,	// this colon should be in math mode
               squash(pp, 3, binop, -2, 123);
         // 3.1.61†
         break;
      }
      pp↑;	// if no match was found, we move to the right
   // 3.1.8†
   }
// 3.1.64†3.1.69: Combine the irreducible scraps that remain
// If the initial sequence of scraps does not reduce to a single scrap, we concatenate the translations of all remaining scraps,
// separated by blank spaces, with dollar signs surrounding the translations of scraps where appropriate.
// †3.1.70: If semi-tracing, show the irreducible scraps
   if (lo_ptr > scrap_base ∧ tracing ≡ 1) {
      printf("\nIrreducible scrap sequence in section %d:", section_count);	// ⁅047⁆
      mark_harmless();
      for (scrap_pointer j = scrap_base; j ≤ lo_ptr; j↑) printf(" "), print_cat(j→cat);
   }
// 3.1.70†
   for (scrap_pointer j = scrap_base; j ≤ lo_ptr; j↑) {
      if (j ≠ scrap_base) app(' ');
      if (j→mathness%4 ≡ yes_math) app('$');
      app1(j);
      if (j→mathness/4 ≡ yes_math) app('$');
      if (tok_ptr + 6 > tok_mem_end) overflow("token");
   }
   freeze_text();
// 3.1.69†
   return text_ptr - 1;
}
// 3.1.68†

// ‡3.2. Initializing the Scraps.
// †3.2.1:
// If we are going to use the powerful production mechanism just developed, we must get the scraps set up in the first place, given a ‹C99› text.
// A table of the initial scraps corresponding to ‹C99› tokens appeared above in the section on parsing;
// our goal now is to implement that table. We shall do this by implementing a subroutine called ≪C_parse≫ that is analogous to the ≪C_xref≫ routine used during phase one.

// Like ≪C_xref≫, the ≪C_parse≫ procedure starts with the current value of ≪next_control≫
// and it uses the operation ≪next_control = get_next()≫ repeatedly to read ‹C99› text
// until encountering the next ‛‹|›’ or ‛‹/*›’, or until ≪next_control ≥ format_code≫.
// */
// The scraps corresponding to what it reads are appended into the ≪cat≫ and ≪trans≫ arrays, and ≪scrap_ptr≫ is advanced.
void C_parse(eight_bits spec_ctrl) {	// creates scraps from ‹C99› tokens
   while (next_control < format_code ∨ next_control ≡ spec_ctrl) {
   // †3.2.3: Append the scrap appropriate to ≪next_control≫
      CheckScrapSpace();	// Make sure that there is room for the new scraps, tokens, and texts
      switch (next_control) {
         case section_name: app(section_flag + (int)(cur_section - name_dir)), app_scrap(section_scrap, maybe_math), app_scrap(exp, yes_math); break;
         case string: case constant: case verbatim: {
         // †3.2.6: Append a string or constant
         // The following code must use ≪app_tok≫ instead of ≪app≫ in order to protect against overflow.
         // Note that ≪tok_ptr + 1 ≤ max_toks≫ after ≪app_tok≫ has been used, so another ≪app≫ is legitimate before testing again.

         // Many of the special characters in a string must be prefixed by ‛\.\\’ so that ‹TeX› will print them properly. ⁅048⁆
            int count = -1;	// characters remaining before string break
            if (next_control ≡ constant) app_str("\\T{"/*}*/);	// ⁅049⁆
            else if (next_control ≡ string) count = 20, app_str("\‹"/*›*/);	// ⁅050⁆
            else app_str("\\vb{"/*}*/);	// ⁅051⁆
            while (id_first < id_loc) {
               if (count ≡ 0)	// insert a discretionary break in a long string
                  app_str(/*(*//*{*/"}\\)\‹"/*›*/), count = 20;	// ⁅052⁆⁅053⁆
               if ((eight_bits)*id_first > 0x7f) app_tok(quoted_char), app_tok((eight_bits)*id_first↑);
               else {
                  switch (*id_first) {
                     case  ' ': case '\\': case '#': case '%': case '$': case '^':
                     case '{': case '}': case '~': case '&': case '_': app('\\'); break;	// ⁅054⁆⁅055⁆⁅056⁆⁅057⁆⁅058⁆⁅059⁆⁅060⁆⁅061⁆⁅062⁆⁅063⁆⁅064⁆
                     case '@':
                        if (*(id_first + 1) ≡ '@') id_first↑;
                        else err_print("! Double @ should be used in strings");	// ⁅065⁆
                     break;
                  }
                  app_tok(*id_first↑);
               }
               count↓;
            }
            app(/*{*/'}'), app_scrap(exp, maybe_math);
         // 3.2.6†
         }
         break;
         case identifier: app_cur_id(1); break;
         case TeX_string:
         // †3.2.7: Append a ‹TeX› string, without forming a scrap
         // We do not make the ‹TeX› string into a scrap, because there is no telling what the user will be putting into it;
         // instead we leave it open, to be picked up by the next scrap.
         // If it comes at the end of a section, it will be made into a scrap when ≪finish_C≫ is called.
         //
         // There's a known bug here, in cases where an adjacent scrap is ≪prelangle≫ or ≪prerangle≫.
         // Then the ‹TeX› string can disappear when the ‹\langle› or ‹\rangle› becomes ‹<› or ‹>›.
         // For example, if the user writes ‹|x<@ty@>|›, the ‹TeX› string ≪\hbox{y}≫ eventually becomes part of an ≪insert≫ scrap,
         // which is combined with a ≪prelangle≫ scrap and eventually lost.
         // The best way to work around this bug is probably to enclose the ‹@t...@>› in ‹@[...@]› so that the ‹TeX› string is treated as an expression. ⁅066⁆
            app_str("\\hbox{"/*}*/);	// ⁅067⁆
            while (id_first < id_loc)
               if ((eight_bits)*id_first > 0x7f) app_tok(quoted_char), app_tok((eight_bits)*id_first↑);
               else {
                  if (*id_first ≡ '@') id_first↑;
                  app_tok(*id_first↑);
               }
            app(/*{*/'}');
         // 3.2.7†
         break;
         case '/': case '.': app(next_control), app_scrap(binop, yes_math); break;
         case '<': app_str("\\langle"), app_scrap(prelangle, yes_math); break;	// ⁅068⁆
         case '>': app_str("\\rangle"), app_scrap(prerangle, yes_math); break;	// ⁅069⁆
         case '=': app_str("\\K"), app_scrap(binop, yes_math); break;	// ⁅070⁆
         case '|': app_str("\\OR"), app_scrap(binop, yes_math); break;	// ⁅071⁆
         case '^': app_str("\\XOR"), app_scrap(binop, yes_math); break;	// ⁅072⁆
         case '%': app_str("\\MOD"), app_scrap(binop, yes_math); break;	// ⁅073⁆
         case '!': app_str("\\R"), app_scrap(unop, yes_math); break;	// ⁅074⁆
         case '~': app_str("\\CM"), app_scrap(unop, yes_math); break;	// ⁅075⁆
         case '+': case '-': app(next_control), app_scrap(ubinop, yes_math); break;
         case '*': app(next_control), app_scrap(raw_ubin, yes_math); break;
         case '&': app_str("\\AND"), app_scrap(raw_ubin, yes_math); break;	// ⁅076⁆
         case '?': app_str("\\?"), app_scrap(question, yes_math); break;	// ⁅077⁆
         case '#': app_str("\\#"), app_scrap(ubinop, yes_math); break;	// ⁅078⁆
         case ignore: case xref_roman: case xref_wildcard:
         case xref_typewriter: case noop: break;
         case '(': case '[': app(next_control), app_scrap(lpar, maybe_math); break;
         case ')': case ']': app(next_control), app_scrap(rpar, maybe_math); break;
         case '{': app_str("\\{"/*}*/), app_scrap(lbrace, yes_math); break;	// ⁅079⁆
         case '}': app_str(/*{*/"\\}"), app_scrap(rbrace, yes_math); break;	// ⁅080⁆
         case ',': app(','), app_scrap(comma, yes_math); break;
         case ';': app(';'), app_scrap(semi, maybe_math); break;
         case ':': app(':'), app_scrap(colon, no_math); break;
// ‹\4›
      // †3.2.5: Cases involving nonstandard characters
      // Some nonstandard characters may have entered ‹CWEAVE› by means of standard ones.
      // They are converted to ‹TeX› control sequences so that it is possible to keep ‹CWEAVE› from outputting unusual ≪char≫ codes.
         case not_eq: app_str("\\I"); app_scrap(binop, yes_math); break;	// ⁅081⁆
         case lt_eq: app_str("\\Z"); app_scrap(binop, yes_math); break;	// ⁅082⁆
         case gt_eq: app_str("\\G"); app_scrap(binop, yes_math); break;	// ⁅083⁆
         case eq_eq: app_str("\\E"); app_scrap(binop, yes_math); break;	// ⁅084⁆
         case and_and: app_str("\\W"); app_scrap(binop, yes_math); break;	// ⁅085⁆
         case or_or: app_str("\\V"); app_scrap(binop, yes_math); break;	// ⁅086⁆
         case plus_plus: app_str("\\PP"); app_scrap(unop, yes_math); break;	// ⁅087⁆
         case minus_minus: app_str("\\MM"); app_scrap(unop, yes_math); break;	// ⁅088⁆
         case minus_gt: app_str("\\MG"); app_scrap(binop, yes_math); break;	// ⁅089⁆
         case gt_gt: app_str("\\GG"); app_scrap(binop, yes_math); break;	// ⁅090⁆
         case lt_lt: app_str("\\LL"); app_scrap(binop, yes_math); break;	// ⁅091⁆
         case dot_dot_dot: app_str("\\,\\ldots\\,"); app_scrap(raw_int, yes_math); break;	// ⁅092⁆⁅093⁆
         case colon_colon: app_str("\\DC"); app_scrap(colcol, maybe_math); break;	// ⁅094⁆
         case period_ast: app_str("\\PA"); app_scrap(binop, yes_math); break;	// ⁅095⁆
         case minus_gt_ast: app_str("\\MGA"); app_scrap(binop, yes_math); break;	// ⁅096⁆
      // 3.2.5†
         case thin_space: app_str("\\,"), app_scrap(insert, maybe_math); break;	// ⁅097⁆
         case math_break: app(opt), app_str("0"), app_scrap(insert, maybe_math); break;
         case line_break: app(force), app_scrap(insert, no_math); break;
         case left_preproc: app(force), app(preproc_line), app_str("\\#"), app_scrap(lproc, no_math); break;	// ⁅098⁆
         case right_preproc: app(force), app_scrap(rproc, no_math); break;
         case big_line_break: app(big_force), app_scrap(insert, no_math); break;
         case no_line_break: app(big_cancel), app(noop), app(break_space), app(noop), app(big_cancel), app_scrap(insert, no_math); break;
         case pseudo_semi: app_scrap(semi, maybe_math); break;
         case macro_arg_open: app_scrap(begin_arg, maybe_math); break;
         case macro_arg_close: app_scrap(end_arg, maybe_math); break;
         case join: app_str("\\J"), app_scrap(insert, no_math); break;	// ⁅099⁆
         case output_defs_code: app(force), app_str("\\ATH"), app(force), app_scrap(insert, no_math); break;	// ⁅100⁆
         default: app(inserted), app(next_control), app_scrap(insert, maybe_math); break;
      }
   // 3.2.3†
      next_control = get_next();
      if (next_control ≡ '|' ∨ next_control ≡ begin_comment ∨ next_control ≡ begin_short_comment) return;
   }
}

// 3.2.1†3.2.2:
// The following macro is used to append a scrap whose tokens have just been appended:
#define app_scrap(c, b) {
   (↑scrap_ptr)→cat = c, scrap_ptr→trans = text_ptr;
   scrap_ptr→mathness = 5*b;	// no no, yes yes, or maybe maybe
   freeze_text();
}

// 3.2.2†3.2.4: [2] Make sure that there is room for the new scraps, tokens, and texts
// Editor's Note:
// ∙	This was orginally a multiply-used module.
inline void CheckScrapSpace(void) {
   if (scrap_ptr + safe_scrap_incr > scrap_info_end ∨ tok_ptr + safe_tok_incr > tok_mem_end ∨ text_ptr + safe_text_incr > tok_start_end) {
      if (scrap_ptr > max_scr_ptr) max_scr_ptr = scrap_ptr;
      if (tok_ptr > max_tok_ptr) max_tok_ptr = tok_ptr;
      if (text_ptr > max_text_ptr) max_text_ptr = text_ptr;
      overflow("scrap/token/text");
   }
}

// 3.2.4†3.2.9:
void app_cur_id(boolean scrapping) {	// are we making this into a scrap?
   name_pointer p = id_lookup(id_first, id_loc, normal);
   if (p→ilk ≤ custom) {	// not a reserved word
      app(id_flag + (int)(p - name_dir));
      if (scrapping) app_scrap(p→ilk ≡ func_template? ftemplate: exp, p→ilk ≡ custom? yes_math: maybe_math);	// ⁅101⁆
   } else {
      app(res_flag + (int)(p - name_dir));
      if (scrapping) {
         if (p→ilk ≡ alfop) app_scrap(ubinop, yes_math) // ;
         else app_scrap(p→ilk, maybe_math);
      }
   }
}

// 3.2.9†3.2.10:
// When the ‛‹|›’ that introduces ‹C99› text is sensed, a call on ≪C_translate≫ will return a pointer to the ‹TeX› translation of that text.
// If scraps exist in ≪scrap_info≫, they are unaffected by this translation process.
text_pointer C_translate(void) {
   scrap_pointer save_base = scrap_base;	// holds original value of ≪scrap_base≫
   scrap_base = scrap_ptr + 1;
   C_parse(section_name);	// get the scraps together
   if (next_control ≠ '≪') err_print("! Missing '≫' after C text");	// ⁅102⁆
   app_tok(cancel); app_scrap(insert, maybe_math);	// place a ≪cancel≫ token as a final ‟comment”
   text_pointer p = translate();	// make the translation and point to it
   if (scrap_ptr > max_scr_ptr) max_scr_ptr = scrap_ptr;
   scrap_ptr = scrap_base - 1; scrap_base = save_base;	// scrap the scraps
   return p;
}

// 3.2.10†3.2.11:
// The ≪outer_parse≫ routine is to ≪C_parse≫ as ≪outer_xref≫ is to ≪C_xref≫:
// It constructs a sequence of scraps for ‹C99› text until ≪next_control ≥ format_code≫.
// Thus, it takes care of embedded comments.

// The token list created from within ‛‹pb›’ brackets is output as an argument to ‹\PB›, if the user has invoked ‹CWEAVE› with the ‹+e› flag.
// Although ‹cwebmac› ignores ‹\PB›, other macro packages might use it to localize the special meaning of the macros that mark up program text.
#define make_pb flags['e']

void outer_parse(void) {	// makes scraps from ‹C99› tokens and comments
   while (next_control < format_code)
      if (next_control ≠ begin_comment ∧ next_control ≠ begin_short_comment) C_parse(ignore);
      else {
         boolean is_long_comment = (next_control ≡ begin_comment);
         CheckScrapSpace();	// Make sure that there is room for the new scraps, tokens, and texts
         app(cancel), app(inserted);
         if (is_long_comment) app_str("\\C{"/*}*/);	// ⁅103⁆
         else app_str("\\SHC{"/*}*/);	// ⁅104⁆
         int bal = copy_comment(is_long_comment, 1);	// brace level in comment
         next_control = ignore;
         while (bal > 0) {
            text_pointer p = text_ptr;	// partial comment
            freeze_text();
            text_pointer q = C_translate();	// partial comment
         // at this point we have ≪tok_ptr + 6 ≤ max_toks≫
            app(tok_flag + (int)(p - tok_start));
            if (make_pb) app_str("\\PB{");	// ⁅105⁆
            app(inner_tok_flag + (int)(q - tok_start));
            if (make_pb) app_tok('}');
            if (next_control ≡ '|') bal = copy_comment(is_long_comment, bal), next_control = ignore;
            else bal = 0;	// an error has been reported
         }
         app(force); app_scrap(insert, no_math);	// the full comment becomes a scrap
      }
}
// 3.2.11†

// ‡3.3. Output of Tokens.
// †3.3.1:
// So far our programs have only built up multi-layered token lists in ‹CWEAVE›'s internal memory;
// we have to figure out how to get them into the desired final form.
// The job of converting token lists to characters in the ‹TeX› output file is not difficult, although it is an implicitly recursive process.
// our main considerations had to be kept in mind when this part of ‹CWEAVE› was designed.
// (a)	There are two modes of output: ≪outer≫ mode, which translates tokens like ≪force≫ into line-breaking control sequences,
//	and ≪inner≫ mode, which ignores them except that blank spaces take the place of line breaks.
// (b)	The ≪cancel≫ instruction applies to adjacent token or tokens that are output,
//	and this cuts across levels of recursion since ‛≪cancel≫’ occurs at the beginning or end of a token list on one level.
// (c)	The ‹TeX› output file will be semi-readable if line breaks are inserted after the result of tokens like ≪break_space≫ and ≪force≫.
// (d)	The final line break should be suppressed, and there should be no ≪force≫ token output immediately after ‛‹\Y\B›’.

// 3.3.1†3.3.5:
// To insert token-list ≪p≫ into the output, the ≪push_level≫ subroutine is called; it saves the old level of output and gets a new one going.
// The value of ≪cur_mode≫ is not changed.
void push_level(text_pointer p) {	// suspends the current level
   if (stack_ptr ≡ stack_end) overflow("stack");
   if (stack_ptr > stack)	// save current state
      stack_ptr→end_field = cur_end, stack_ptr→tok_field = cur_tok, stack_ptr→mode_field = cur_mode;
   if (↑stack_ptr > max_stack_ptr) max_stack_ptr = stack_ptr;
   cur_tok = *p, cur_end = *(p + 1);
}

// 3.3.5†3.3.6:
// Conversely, the ≪pop_level≫ routine restores the conditions that were in force when the current level was begun.
// This subroutine will never be called when ≪stack_ptr ≡ 1≫.
void pop_level(void) {
   cur_end = (↓stack_ptr)→end_field, cur_tok = stack_ptr→tok_field, cur_mode = stack_ptr→mode_field;
}

// 3.3.6†3.3.8:
#define res_word	0x81	// returned by ≪get_output≫ for reserved words
#define section_code	0x80	// returned by ≪get_output≫ for section names

eight_bits get_output(void) {	// returns the next token of output
restart:
   while (cur_tok ≡ cur_end) pop_level();
   sixteen_bits a = *cur_tok↑;	// current item read from ≪tok_mem≫
   if (a ≥ 0x100) {
      cur_name = a%id_flag + name_dir;
      switch (a/id_flag) {
         case 2: return res_word;	// ≪a ≡ res_flag + cur_name≫
         case 3: return section_code;	// ≪a ≡ section_flag + cur_name≫
         case 4: push_level(a%id_flag + tok_start); goto restart;	// ≪a ≡ tok_flag + cur_name≫
         case 5: push_level(a%id_flag + tok_start); cur_mode = inner; goto restart;	// ≪a ≡ inner_tok_flag + cur_name≫
         default: return identifier;	// ≪a ≡ id_flag + cur_name≫
      }
   }
   return a;
}

// 3.3.8†3.3.9:
// The real work associated with token output is done by ≪make_output≫.
// This procedure appends an ≪end_translation≫ token to the current token list,
// and then it repeatedly calls ≪get_output≫ and feeds characters to the output buffer until reaching the ≪end_translation≫ sentinel.
// It is possible for ≪make_output≫ to be called recursively, since a section name may include embedded ‹C99› text;
// however, the depth of recursion never exceeds one level, since section names cannot be inside of section names.

// A procedure called ≪output_C≫ does the scanning, translation, and output of ‹C99› text within ‛‹pb›’ brackets,
// and this procedure uses ≪make_output≫ to output the current token list.
// Thus, the recursive call of ≪make_output≫ actually occurs when ≪make_output≫ calls ≪output_C≫ while outputting the name of a section. ⁅106⁆

void output_C(void) {	// outputs the current token list
   token_pointer save_tok_ptr = tok_ptr;
   text_pointer save_text_ptr = text_ptr;
   sixteen_bits save_next_control = next_control;	// values to be restored
   next_control = ignore;
   text_pointer p = C_translate();	// translation of the ‹C99› text
   app(inner_tok_flag + (int)(p - tok_start));
   if (make_pb) out_str("\\PB{"), make_output(), out('}');	// ⁅107⁆
   else make_output();	// output the list
   if (text_ptr > max_text_ptr) max_text_ptr = text_ptr;
   if (tok_ptr > max_tok_ptr) max_tok_ptr = tok_ptr;
   text_ptr = save_text_ptr; tok_ptr = save_tok_ptr;	// forget the tokens
   next_control = save_next_control;	// restore ≪next_control≫ to original state
}

// 3.3.9†3.3.11:
void make_output(void) {	// outputs the equivalents of tokens
   app(end_translation);	// append a sentinel
   freeze_text(), push_level(text_ptr - 1);
   while (1) {
      eight_bits a = get_output();	// current output byte
   reswitch:
      switch (a) {
         case end_translation: return;
         case identifier: case res_word:
         // †3.3.12: Output an identifier
         // An identifier of length one does not have to be enclosed in braces,
         // and it looks slightly better if set in a math-italic font instead of a (slightly narrower) text-italic font.
         // Thus we output ‛‹\|a›’ but ‛≪\\{aa}≫’.
            out('\\');
            if (a ≡ identifier) {
               if (cur_name→ilk ≡ custom ∧ !doing_format) {
               custom_out:
               // p: index into ≪byte_mem≫
                  for (char *p = cur_name→byte_start; p < (cur_name + 1)→byte_start; p↑) out(*p ≡ '_'? 'x': *p ≡ '$'? 'X': *p);
                  break;
               } else if (is_tiny(cur_name)) out('|');	// ⁅108⁆
               else {
                  char delim = '.';	// first and last character of string being copied
               // p: index into ≪byte_mem≫
                  for (char *p = cur_name→byte_start;p < (cur_name + 1)→byte_start; p↑)
                     if (xislower(*p)) {	// not entirely uppercase
                        delim = '\\'; break;
                     }
                  out(delim);
               }	// ⁅109⁆⁅110⁆
            } else if (cur_name→ilk ≡ alfop) out('X'), goto custom_out;
            else out('&');	// ≪a ≡ res_word≫ ⁅111⁆
            if (is_tiny(cur_name)) {
               if (isxalpha((cur_name→byte_start)[0])) out('\\');
               out((cur_name→byte_start)[0]);
            } else out_name(cur_name, 1);
         // 3.3.12†
         break;
         case section_code: {
         // †3.3.16: Output a section name
         // The remaining part of ≪make_output≫ is somewhat more complicated.
         // When we output a section name, we may need to enter the parsing and translation routines,
         // since the name may contain ‹C99› code embedded in ‹pb› constructions.
         // This ‹C99› code is placed at the end of the active input buffer and the translation process uses the end of the active ≪tok_mem≫ area.
            out_str("\\X");	// ⁅112⁆
            cur_xref = (xref_pointer)cur_name→xref;
            an_output = cur_xref→num ≡ file_flag;
            if (an_output) cur_xref = cur_xref→xlink;
            if (cur_xref→num ≥ def_flag) {
               out_section(cur_xref→num - def_flag);
               if (phase ≡ 3) {
                  cur_xref = cur_xref→xlink;
                  while (cur_xref→num ≥ def_flag) out_str(", "), out_section(cur_xref→num - def_flag), cur_xref = cur_xref→xlink;
               }
            } else out('0');	// output the section number, or zero if it was undefined
            out(':');
            if (an_output) out_str("\‹"/*›*/);	// ⁅113⁆
         // †3.3.17: Output the text of the section name
            char scratch[longest_name];	// scratch area for section names
            sprint_section_name(scratch, cur_name);
            name_pointer cur_section_name = cur_name;	// name of section being output
            for (char *k = scratch, *k_limit = scratch + strlen(scratch); k < k_limit; ) { // k, k_limit: indices into ≪scratch≫
               eight_bits b = *k↑;	// next output byte
               if (b ≡ '@')
               // †3.3.18: Skip next character, give error if not ‛‹@›’
                  if (*k↑ ≠ '@') printf("\n! Illegal control code in section name: <"), print_section_name(cur_section_name), printf("> "), mark_error();	// ⁅114⁆
               // 3.3.18†
               if (an_output) switch (b) {
                  case ' ': case '\\': case '#': case '%': case '$': case '^':
                  case '{': case '}': case '~': case '&': case '_':
                     out('\\');	// ⁅115⁆⁅116⁆⁅117⁆⁅118⁆⁅119⁆⁅120⁆⁅121⁆⁅122⁆⁅123⁆⁅124⁆⁅125⁆
                  default:
                     out(b);
                  break;
               } else if (b ≠ '|') out(b) // ;
               else {
               // †3.3.19: Copy the ‹C99› text into the ≪buffer≫ array
               // The ‹C99› text enclosed in ‹pb› should not contain ‛‹|›’ characters, except within strings.
               // We put a ‛‹|›’ at the front of the buffer, so that an error message that displays the whole buffer will look a little bit sensible.
               // The variable ≪delim≫ is zero outside of strings, otherwise it equals the delimiter that began the string being copied.
                  char *j = limit + 1;	// index into ≪buffer≫
                  *j = '|';
                  char delim = 0;	// first and last character of string being copied
                  while (1) {
                     if (k ≥ k_limit) {
                        printf("\n! C text in section name didn't end: <"),	// ⁅126⁆
                        print_section_name(cur_section_name), printf("> "), mark_error(); break;
                     }
                     eight_bits b = *k↑;	// next output byte
                     if (b ≡ '@' ∨ b ≡ '\\' ∧ delim ≠ 0) {
                     // †3.3.20: Copy a quoted character into the buffer
                        if (j > buffer + long_buf_size - 4) overflow("buffer");
                        *↑j = b, *↑j = *k↑;
                     // 3.3.20†
                     } else {
                        if (b ≡ '\'' ∨ b ≡ '"')
                           if (delim ≡ 0) delim = b;
                           else if (delim ≡ b) delim = 0;
                        if (b ≠ '|' ∨ delim ≠ 0) {
                           if (j > buffer + long_buf_size - 3) overflow("buffer");
                           *↑j = b;
                        } else break;
                     }
                  }
               // 3.3.19†
                  char *save_loc = loc, *save_limit = limit;	// ≪loc≫ and ≪limit≫ to be restored
                  loc = limit + 2, limit = j + 1;
                  *limit = '|', output_C(), loc = save_loc, limit = save_limit;
               }
            }
         // 3.3.17†
            if (an_output) out_str(/*{*/" }");
            out_str("\\X");
         // 3.3.16†
         }
         break;
         case math_rel: out_str("\\MRL{"/*}*/);	// ⁅127⁆
         case noop: case inserted: break;
         case cancel: case big_cancel: {
            int c = 0;	// count of ≪indent≫ and ≪outdent≫ tokens
            eight_bits b = a;	// next output byte
            while (1) {
               a = get_output();
               if (a ≡ inserted) continue;
               if (a < indent ∧ !(b ≡ big_cancel ∧ a ≡ ' ') ∨ a > big_force) break;
               if (a ≡ indent) c↑; else if (a ≡ outdent) c↓;
               else if (a ≡ opt) a = get_output();
            }
            PutDent(c); // Output saved ≪indent≫ or ≪outdent≫ tokens
         }
         goto reswitch;
         case indent: case outdent: case opt: case backup: case break_space:
         case force: case big_force: case preproc_line:
         // †3.3.13: Output a control, look ahead in case of line breaks, possibly ≪goto reswitch≫
         // The current mode does not affect the behavior of ‹CWEAVE›'s output routine except when we are outputting control tokens.
            if (a < break_space ∨ a ≡ preproc_line) {
               if (cur_mode ≡ outer) {
                  out('\\'), out(a - cancel + '0');	// ⁅128⁆⁅129⁆⁅130⁆⁅131⁆⁅132⁆
                  if (a ≡ opt) {
                     eight_bits b = get_output();	// ≪opt≫ is followed by a digit
                     if (b ≠ '0' ∨ force_lines ≡ 0) out(b) // ;
                     else out_str("{-1}");	// ≪force_lines≫ encourages more ‹@|› breaks
                  }
               } else if (a ≡ opt) b = get_output();	// ignore digit following ≪opt≫
            } else {
            // †3.3.14: Look ahead for strongest line break, ≪goto reswitch≫
            // If several of the tokens ≪break_space≫, ≪force≫, ≪big_force≫ occur in a row, possibly mixed with blank spaces (which are ignored), the largest one is used.
            // A line break also occurs in the output file, except at the very end of the translation.
            // The very first line break is suppressed (i.e., a line break that follows ‛‹\Y\B›’).
               eight_bits b = a;	// next output byte
               boolean save_mode = cur_mode;	// value of ≪cur_mode≫ before a sequence of breaks
               int c = 0;	// count of ≪indent≫ and ≪outdent≫ tokens
               while (1) {
                  a = get_output();
                  if (a ≡ inserted) continue;
                  else if (a ≡ cancel ∨ a ≡ big_cancel) {
                     PutDent(c); // Output saved ≪indent≫ or ≪outdent≫ tokens
                     break;	// ≪cancel≫ overrides everything
                  } else if (a ≠ ' ' ∧ a < indent ∨ a ≡ backup ∨ a > big_force) {
                     if (save_mode ≡ outer) {
                        if (out_ptr > out_buf + 3 ∧ strncmp(out_ptr - 3, "\\Y\\B", 4) ≡ 0) break;
                        PutDent(c); // Output saved ≪indent≫ or ≪outdent≫ tokens
                        out('\\'), out(b - cancel + '0');	// ⁅133⁆⁅134⁆⁅135⁆
                        if (a ≠ end_translation) finish_line();
                     } else if (a ≠ end_translation ∧ cur_mode ≡ inner) out(' ');
                     break;
                  } else if (a ≡ indent) c↑;
                  else if (a ≡ outdent) c↓;
                  else if (a ≡ opt) a = get_output();
                  else if (a > b) b = a;	// if ≪a ≡ ' '≫ we have ≪a < b≫
               }
            // 3.3.14†
               goto reswitch;
            }
         // 3.3.13†
         break;
         case quoted_char: out(*(cur_tok↑));
         case qualifier: break;
         default: out(a);	// otherwise ≪a≫ is an ordinary character
      }
   }
}

// 3.3.11†3.3.15: [3] Output saved ≪indent≫ or ≪outdent≫ tokens
// Editor's Note:
// ∙	This was orginally a multiply-used module.
inline void PutDent(int c) {
   for (; c > 0; c↓) out_str("\\1");	// ⁅136⁆
   for (; c < 0; c↑) out_str("\\2");	// ⁅137⁆
}
// 3.3.15†

// §4. Phase Two Processing.
// †4.2:
void phase_two(void) {
   reset_input(); if (show_progress) printf("\nWriting the output file...");	// ⁅138⁆
   section_count = 0, format_visible = 1, copy_limbo();
   finish_line(), flush_buffer(out_buf, 0, 0);	// insert a blank line, it looks nice
   while (!input_has_ended) {
   // †4.4: Translate the current section
      section_count↑;
   // †4.5: Output the code for the beginning of a new section
   // Sections beginning with the ‹CWEB› control sequence ‛‹@ ›’ start in the output with the ‹TeX› control sequence ‛‹\M›’, followed by the section number.
   // Similarly, ‛‹@*›’ sections lead to the control sequence ‛‹\N›’.
   // In this case there's an additional parameter, representing one plus the specified depth, immediately after the ‹\N›.
   // If the section has changed, we put ‹\*› just after the section number.
      if (*(loc - 1) ≠ '*') out_str("\\M");	// ⁅139⁆
      else {
         while (*loc ≡ ' ') loc↑;
         if (*loc ≡ '*')	// ‟top” level
            sec_depth = -1, loc↑;
         else for (sec_depth = 0; xisdigit(*loc); loc↑) sec_depth = 10*sec_depth + *loc - '0';
         for (; *loc ≡ ' '; loc↑);	// remove spaces before group title
         group_found = 1;
         out_str("\\N");	// ⁅140⁆
         char s[0x20]; sprintf(s, "{%d}", sec_depth + 1), out_str(s);
         if (show_progress) printf("*%d", section_count);
         update_terminal();	// print a progress report
      }
      out_str("{"), out_section(section_count), out_str("}");
   // 4.5†
      save_position();
   // †4.6: Translate the ‹TeX› part of the current section
   // In the ‹TeX› part of a section, we simply copy the source text, except that index entries are not copied and ‹C99› text within ‹pb› is translated.
      do {
         next_control = copy_TeX();
         switch (next_control) {
            case '|': init_stack(), output_C(); break;
            case '@': out('@'); break;
            case TeX_string: case noop:
            case xref_roman: case xref_wildcard: case xref_typewriter:
            case section_name:
               loc -= 2; next_control = get_next();	// skip to ‹@>›
               if (next_control ≡ TeX_string) err_print("! TeX string should be in C text only");
            break;	// ⁅141⁆
            case thin_space: case math_break: case ord:
            case line_break: case big_line_break: case no_line_break: case join:
            case pseudo_semi: case macro_arg_open: case macro_arg_close:
            case output_defs_code: err_print("! You can't do that in TeX text"); break;	// ⁅142⁆
         }
      } while (next_control < format_code);
   // 4.6†4.7: Translate the definition part of the current section
   // When we get to the following code we have ≪next_control ≥ format_code≫, and the token memory is in its initial empty state.
      space_checked = 0;
      while (next_control ≤ definition) {	// ≪format_code≫ or ≪definition≫
         init_stack();
         if (next_control ≡ definition) {
         // †4.10: Start a macro definition
         // Keeping in line with the conventions of the ‹C99› preprocessor (and otherwise contrary to the rules of ‹CWEB›)
         // we distinguish here between the case that ‛‹(›’ immediately follows an identifier and the case that the two are separated by a space.
         // In the latter case, and if the identifier is not followed by ‛‹(›’ at all, the replacement text starts immediately after the identifier.
         // In the former case, it starts after we scan the matching ‛‹)›’.
            if (save_line ≠ out_line ∨ save_place ≠ out_ptr ∨ space_checked) app(backup);
            if (!space_checked) emit_space_if_needed(), save_position();
            app_str("\\D");	// this will produce ‛«define »’ ⁅143⁆
            next_control = get_next();
            if (next_control ≠ identifier) err_print("! Improper macro definition");	// ⁅144⁆
            else {
               app('$'), app_cur_id(0);
               if (*loc ≡ '(')
               reswitch:
               switch (next_control = get_next()) {
                  case '(': case ',': app(next_control); goto reswitch;
                  case identifier: app_cur_id(0); goto reswitch;
                  case ')': app(next_control); next_control = get_next(); break;
                  default: err_print("! Improper macro definition"); break;
               } else next_control = get_next();
               app_str("$ "), app(break_space), app_scrap(dead, no_math);	// scrap won't take part in the parsing
            }
         // 4.10†
         } else {
         // †4.11: Start a format definition
            doing_format = 1;
            if (*(loc - 1) ≡ 's' ∨ *(loc - 1) ≡ 'S') format_visible = 0;
            if (!space_checked) emit_space_if_needed(), save_position();
            app_str("\\F");	// this will produce ‛«format »’ ⁅145⁆
            next_control = get_next();
            if (next_control ≡ identifier) {
               app(id_flag + (int)(id_lookup(id_first, id_loc, normal) - name_dir)), app(' ');
               app(break_space);	// this is syntactically separate from what follows
               next_control = get_next();
               if (next_control ≡ identifier)
                  app(id_flag + (int)(id_lookup(id_first, id_loc, normal) - name_dir)),
                  app_scrap(exp, maybe_math), app_scrap(semi, maybe_math),
                  next_control = get_next();
            }
            if (scrap_ptr ≠ scrap_info + 2) err_print("! Improper format definition");	// ⁅146⁆
         // 4.11†
         }
         outer_parse(); finish_C(format_visible); format_visible = 1;
         doing_format = 0;
      }
   // 4.7†4.13: Translate the ‹C99› part of the current section
      this_section = name_dir;
      if (next_control ≤ section_name) {
         emit_space_if_needed(), init_stack();
         if (next_control ≡ begin_C) next_control = get_next();
         else {
            this_section = cur_section;
         // †4.14: Check that '=' or '==' follows this section name, and emit the scraps to start the section definition
         // The title of the section and an \E or \mathrel + \E are made into a scrap that should not take part in the parsing.
            do next_control = get_next(); while (next_control ≡ '+');	// allow optional ‛‹+=›’
            if (next_control ≠ '=' ∧ next_control ≠ eq_eq) err_print("! You need an = sign after the section name");	// ⁅147⁆
            else next_control = get_next();
            if (out_ptr > out_buf + 1 ∧ *out_ptr ≡ 'Y' ∧ *(out_ptr - 1) ≡ '\\') app(backup);	// the section name will be flush left ⁅148⁆
            app(section_flag + (int)(this_section - name_dir));
            cur_xref = (xref_pointer)this_section→xref;
            if (cur_xref→num ≡ file_flag) cur_xref = cur_xref→xlink;
            app_str("${}");
            if (cur_xref→num ≠ section_count + def_flag)
               app_str("\\mathrel+"),	// section name is multiply defined
               this_section = name_dir;	// so we won't give cross-reference info here
            app_str("\\E");	// output an equivalence sign ⁅149⁆
            app_str("{}$");
            app(force), app_scrap(dead, no_math);	// this forces a line break unless ‛‹@+›’ follows
         // 4.14†
         }
         while (next_control ≤ section_name) {
            outer_parse();
         // †4.15: Emit the scrap for a section name if present
            if (next_control < section_name)
               err_print("! You can't do that in C text"),	// ⁅150⁆
               next_control = get_next();
            else if (next_control ≡ section_name)
               app(section_flag + (int)(cur_section - name_dir)),
               app_scrap(section_scrap, maybe_math),
               next_control = get_next();
         // 4.15†
         }
         finish_C(1);
      }
   // 4.13†4.16: Show cross-references to this section
   // Cross references relating to a named section are given after the section ends.
      if (this_section > name_dir) {
         cur_xref = (xref_pointer)this_section→xref;
         if (cur_xref→num ≡ file_flag) an_output = 1, cur_xref = cur_xref→xlink;
         else an_output = 0;
         if (cur_xref→num > def_flag) cur_xref = cur_xref→xlink;	// bypass current section number
         footnote(def_flag), footnote(cite_flag), footnote(0);
      }
   // 4.16†4.20: Output the code for the end of a section
      out_str("\\fi"), finish_line();	// ⁅151⁆
      flush_buffer(out_buf, 0, 0);	// insert a blank line, it looks nice
   // 4.20†
   // 4.4†
   }
}

// 4.2†4.9:
// visible: nonzero if we should produce ‹TeX› output
void finish_C(boolean visible) {	// finishes a definition or a ‹C99› part
   if (visible) {
      out_str("\\B"), app_tok(force), app_scrap(insert, no_math);
      text_pointer p = translate();	// translation of the scraps ⁅152⁆
      app(tok_flag + (int)(p - tok_start)), make_output();	// output the list
      if (out_ptr > out_buf + 1)
         if (*(out_ptr - 1) ≡ '\\')	// ⁅153⁆⁅154⁆⁅155⁆
            if (*out_ptr ≡ '6') out_ptr -= 2;
            else if (*out_ptr ≡ '7') *out_ptr = 'Y';
      out_str("\\par"), finish_line();
   }
   if (text_ptr > max_text_ptr) max_text_ptr = text_ptr;
   if (tok_ptr > max_tok_ptr) max_tok_ptr = tok_ptr;
   if (scrap_ptr > max_scr_ptr) max_scr_ptr = scrap_ptr;
   tok_ptr = tok_mem + 1, text_ptr = tok_start + 1, scrap_ptr = scrap_info;	// forget the tokens and the scraps
}

// 4.9†4.18:
void footnote(sixteen_bits flag) {	// outputs section cross-references
   if (cur_xref→num ≤ flag) return;
   finish_line(), out('\\');	// ⁅156⁆⁅157⁆⁅158⁆
   out(flag ≡ 0? 'U': flag ≡ cite_flag? 'Q': 'A');
// †4.19: Output all the section numbers on the reference list ≪cur_xref≫
// The following code distinguishes three cases, according as the number of cross-references is one, two, or more than two.
// Variable ≪q≫ points to the first cross-reference, and the last link is a zero.
   xref_pointer q = cur_xref;	// cross-reference pointer variable
   if (q→xlink→num > flag) out('s');	// plural
   while (1) {
      out_section(cur_xref→num - flag);
      cur_xref = cur_xref→xlink;	// point to the next cross-reference to output
      if (cur_xref→num ≤ flag) break;
      if (cur_xref→xlink→num > flag) out_str(", ");	// not the last
      else {
         out_str("\\ET");	// the last ⁅159⁆
         if (cur_xref ≠ q→xlink) out('s');	// the last of more than two
      }
   }
// 4.19†
   out('.');
}
// 4.18†

// §5. Phase Three Processing.
// †5.2:
void phase_three(void) {
   if (no_xref)
      finish_line(), out_str("\\end"),	// ⁅160⁆
      finish_line();
   else {
      phase = 3; if (show_progress) printf("\nWriting the index...");	// ⁅161⁆
      finish_line();
      idx_file = fopen(idx_file_name, "w"); if (idx_file ≡ NULL) fatal("! Cannot open index file ", idx_file_name);	// ⁅162⁆
      if (change_exists) {
      // †5.4: Tell about changed sections
      // remember that the index is already marked as changed
         k_section = 0;
         while (!changed_section[↑k_section]);
         out_str("\\ch ");	// ⁅163⁆
         out_section(k_section);
         while (k_section < section_count) {
            while (!changed_section[↑k_section]);
            out_str(", "), out_section(k_section);
         }
         out('.');
      // 5.4†
         finish_line(), finish_line();
      }
      out_str("\\inx"); finish_line();	// ⁅164⁆
      active_file = idx_file;	// change active file to the index file
   // †5.6: Do the first pass of sorting
   // To begin the sorting, we go through all the hash lists and put each entry having a nonempty cross-reference list into the proper bucket.
      for (int c = 0; c ≤ 0xff; c↑) bucket[c] = NULL;
      for (h = hash; h ≤ hash_end; h↑) {
         next_name = *h;
         while (next_name) {
            cur_name = next_name, next_name = cur_name→link;
            if (cur_name→xref ≠ (char *)xmem) {
               int c = (eight_bits)((cur_name→byte_start)[0]);
               if (xisupper(c)) c = tolower(c);
               blink[cur_name - name_dir] = bucket[c], bucket[c] = cur_name;
            }
         }
      }
   // 5.6†5.15: Sort and output the index
      sort_ptr = scrap_info; unbucket(1);
      while (sort_ptr > scrap_info) {
         cur_depth = sort_ptr→depth;
         if (blink[sort_ptr→head - name_dir] ≡ 0 ∨ cur_depth ≡ infinity) {
         // †5.17: Output index entries for the list at ≪sort_ptr≫
            cur_name = sort_ptr→head;
            do {
               out_str("\\I");	// ⁅165⁆
            // †5.18: Output the name at ≪cur_name≫
               switch (cur_name→ilk) {
                  case normal: case func_template:
                     if (is_tiny(cur_name)) out_str("\\|");
                     else {
                        for (char *j = cur_name→byte_start; j < (cur_name + 1)→byte_start; j↑) if (xislower(*j)) goto lowcase;
                        out_str("\\.");
                        break;
                     lowcase:
                        out_str("\\\\");
                     }
                  break;	// ⁅166⁆⁅167⁆⁅168⁆
                  case wildcard: out_str("\\9");  goto not_an_identifier;	// ⁅169⁆
                  case typewriter: out_str("\\.");	// ⁅170⁆
                  case roman: not_an_identifier: out_name(cur_name, 0); goto name_done;
                  case custom: {
                     out_str("$\\");
                     for (char *j = cur_name→byte_start; j < (cur_name + 1)→byte_start; j↑) out(*j ≡ '_'? 'x': *j ≡ '$'? 'X': *j);
                     out('$');
                     goto name_done;
                  }
                  default: out_str("\\&"); break;	// ⁅171⁆
               }
               out_name(cur_name, 1);
            name_done: // ;
            // 5.18†
            // †5.19: Output the cross-references at ≪cur_name≫
            // Section numbers that are to be underlined are enclosed in ‛‹\[ … ]›’.
            // †5.21: Invert the cross-reference list at ≪cur_name≫, making ≪cur_xref≫ the head
               this_xref = (xref_pointer)cur_name→xref, cur_xref = xmem;
               do
                  next_xref = this_xref→xlink, this_xref→xlink = cur_xref, cur_xref = this_xref, this_xref = next_xref;
               while (this_xref ≠ xmem);
            // 5.21†
               do {
                  out_str(", "), cur_val = cur_xref→num;
                  if (cur_val < def_flag) out_section(cur_val);
                  else out_str("\\["), out_section(cur_val - def_flag), out(']');	// ⁅172⁆
                  cur_xref = cur_xref→xlink;
               } while (cur_xref  ≠  xmem);
               out('.'), finish_line();
            // 5.19†
               cur_name = blink[cur_name - name_dir];
            } while (cur_name);
            sort_ptr↓;
         // 5.17†
         } else {
         // †5.16: Split the list at ≪sort_ptr≫ into further lists
            next_name = sort_ptr→head;
            do {
               cur_name = next_name, next_name = blink[cur_name - name_dir], cur_byte = cur_name→byte_start + cur_depth;
               eight_bits c;
               if (cur_byte ≡ (cur_name + 1)→byte_start) c = '\0';	// hit end of the name
               else {
                  c = (eight_bits)*cur_byte;
                  if (xisupper(c)) c = tolower(c);
               }
               blink[cur_name - name_dir] = bucket[c], bucket[c] = cur_name;
            } while (next_name);
            sort_ptr↓, unbucket(cur_depth + 1);
         // 5.16†
         }
      }
   // 5.15†
      finish_line(), fclose(active_file);	// finished with ≪idx_file≫
      active_file = tex_file;	// switch back to ≪tex_file≫ for a tic
      out_str("\\fin"), finish_line();	// ⁅173⁆
      scn_file = fopen(scn_file_name, "w");
      if (scn_file ≡ NULL) fatal("! Cannot open section file ", scn_file_name);	// ⁅174⁆
      active_file = scn_file;	// change active file to section listing file
   // †5.24: Output all the section names
      section_print(root)
   // 5.24†
      finish_line(), fclose(active_file);	// finished with ≪scn_file≫
      active_file = tex_file, out_str(group_found? "\\con": "\\end");	// ⁅175⁆⁅176⁆
      finish_line(), fclose(active_file);
   }
   if (show_happiness) printf("\nDone.");
   check_complete();	// was all of the change file used?
}

// 5.2†5.7:
// During the sorting phase we shall use the ≪cat≫ and ≪trans≫ arrays from ‹CWEAVE›'s parsing algorithm and rename them ≪depth≫ and ≪head≫.
// They now represent a stack of identifier lists for all the index entries that have not yet been output.
// The variable ≪sort_ptr≫ tells how many such lists are present;
// the lists are output in reverse order (first ≪sort_ptr≫, then ≪sort_ptr - 1≫, etc.).
// The ≪j≫th list starts at ≪head[j]≫, and if the first ≪k≫ characters of all entries on this list are known to be equal we have ≪depth[j] ≡ k≫.

// 5.7†5.14:
void unbucket(eight_bits d) {	// empties buckets having depth ≪d≫
   for (int c = 100 + 128; c ≥ 0; c↓) if (bucket[collate[c]]) {
   // c is a index into ≪bucket≫ and cannot be a simple ≪char≫ because of sign comparison. ⁅177⁆
      if (sort_ptr ≥ scrap_info_end) overflow("sorting");
      if (↑sort_ptr > max_sort_ptr) max_sort_ptr = sort_ptr;
      sort_ptr→depth = c ≡ 0? infinity: d, sort_ptr→head = bucket[collate[c]], bucket[collate[c]] = NULL;
   }
}

// 5.14†5.23:
void section_print(name_pointer p) {	// print all section names in subtree ≪p≫
   if (p ≠ NULL) {
      section_print(p→llink); out_str("\\I");	// ⁅178⁆
      tok_ptr = tok_mem + 1, text_ptr = tok_start + 1, scrap_ptr = scrap_info, init_stack();
      app(p - name_dir + section_flag); make_output();
      footnote(cite_flag);
      footnote(0);	// ≪cur_xref≫ was set by ≪make_output≫
      finish_line();
      section_print(p→rlink);
   }
}

// 5.23†5.25:
// Because on some systems the difference between two pointers is a ≪long≫ rather than an ≪int≫, we use ‹\%ld› to print these quantities.
void print_stats(void) {
   printf("\nMemory usage statistics:\n");	// ⁅179⁆
   printf("%ld names (out of %ld)\n", (long)(name_ptr - name_dir), (long)max_names);
   printf("%ld cross - references (out of %ld)\n", (long)(xref_ptr - xmem), (long)max_refs);
   printf("%ld bytes (out of %ld)\n", (long)(byte_ptr - byte_mem), (long)max_bytes);
   printf("Parsing:\n");
   printf("%ld scraps (out of %ld)\n", (long)(max_scr_ptr - scrap_info), (long)max_scraps);
   printf("%ld texts (out of %ld)\n", (long)(max_text_ptr - tok_start), (long)max_texts);
   printf("%ld tokens (out of %ld)\n", (long)(max_tok_ptr - tok_mem), (long)max_toks);
   printf("%ld levels (out of %ld)\n", (long)(max_stack_ptr - stack), (long)stack_size);
   printf("Sorting:\n");
   printf("%ld levels (out of %ld)\n", (long)(max_sort_ptr - scrap_info), (long)max_scraps);
}
// 5.25†

// §6. Index.
// †6.1:
// If you have read and understood the code for Phase III above, you know what is in this index and how it got here.
// All sections in which an identifier is used are listed with that identifier, except that reserved words are indexed only when they appear in format definitions,
// and the appearances of identifiers in section names are not indexed.
// Underlined entries correspond to where the identifier was declared.
// Error messages, control sequences put into the output, and a few other things like ‟recursion” are indexed here too.
//	⇔	\*				―	⁅028⁆
//	⇔	\$				―	⁅029⁆⁅058⁆⁅119⁆
//	⇔	\_				―	⁅030⁆⁅064⁆⁅125⁆
//	⇔	\,				―	⁅040⁆⁅041⁆⁅042⁆⁅044⁆⁅046⁆⁅092⁆⁅097⁆
//	⇔	\ 				―	⁅045⁆⁅054⁆⁅115⁆
//	⇔	\\				―	⁅055⁆⁅109⁆⁅116⁆⁅168⁆
//	⇔	\.				―	⁅050⁆⁅110⁆⁅113⁆⁅167⁆⁅170⁆
//	⇔	\)				―	⁅052⁆
//	⇔	\#				―	⁅056⁆⁅078⁆⁅098⁆⁅117⁆
//	⇔	\%				―	⁅057⁆⁅118⁆
//	⇔	\^				―	⁅059⁆⁅120⁆
//	⇔	\{				―	⁅060⁆⁅079⁆⁅121⁆
//	⇔	\}				―	⁅061⁆⁅080⁆⁅122⁆
//	⇔	\~				―	⁅062⁆⁅123⁆
//	⇔	\&				―	⁅063⁆⁅111⁆⁅124⁆⁅171⁆
//	⇔	\?				―	⁅077⁆
//	⇔	\|				―	⁅108⁆⁅166⁆
//	⇔	\[				―	⁅172⁆
//	⇔	\1				―	⁅128⁆⁅136⁆
//	⇔	\2				―	⁅129⁆⁅137⁆
//	⇔	\3				―	⁅130⁆
//	⇔	\4				―	⁅131⁆
//	⇔	\5				―	⁅043⁆⁅133⁆
//	⇔	\6				―	⁅134⁆⁅153⁆
//	⇔	\7				―	⁅135⁆⁅154⁆
//	⇔	\8				―	⁅132⁆
//	⇔	\9				―	⁅169⁆
//	⇔	\A				―	⁅156⁆
//	⇔	\AND				―	⁅076⁆
//	⇔	\ATH				―	⁅100⁆
//	⇔	\ATL				―	⁅031⁆
//	⇔	\B				―	⁅152⁆
//	⇔	\C				―	⁅103⁆
//	⇔	\ch				―	⁅163⁆
//	⇔	\CM				―	⁅075⁆
//	⇔	\con				―	⁅175⁆
//	⇔	\D				―	⁅143⁆
//	⇔	\DC				―	⁅094⁆
//	⇔	\E				―	⁅084⁆⁅149⁆
//	⇔	\end				―	⁅160⁆⁅176⁆
//	⇔	\ET				―	⁅159⁆
//	⇔	\F				―	⁅145⁆
//	⇔	\fi				―	⁅151⁆
//	⇔	\fin				―	⁅173⁆
//	⇔	\G				―	⁅083⁆
//	⇔	\GG				―	⁅090⁆
//	⇔	\I				―	⁅081⁆⁅165⁆⁅178⁆
//	⇔	\inx				―	⁅164⁆
//	⇔	\J				―	⁅099⁆
//	⇔	\K				―	⁅070⁆
//	⇔	\langle				―	⁅068⁆
//	⇔	\ldots				―	⁅093⁆
//	⇔	\LL				―	⁅091⁆
//	⇔	\M				―	⁅139⁆
//	⇔	\MG				―	⁅089⁆
//	⇔	\MGA				―	⁅096⁆
//	⇔	\MM				―	⁅088⁆
//	⇔	\MOD				―	⁅073⁆
//	⇔	\MRL				―	⁅127⁆
//	⇔	\N				―	⁅140⁆
//	⇔	\NULL				―	⁅101⁆
//	⇔	\OR				―	⁅071⁆
//	⇔	\PA				―	⁅095⁆
//	⇔	\PB				―	⁅105⁆⁅107⁆
//	⇔	\PP				―	⁅087⁆
//	⇔	\Q				―	⁅157⁆
//	⇔	\R				―	⁅074⁆
//	⇔	\rangle				―	⁅069⁆
//	⇔	\SHC				―	⁅104⁆
//	⇔	\T				―	⁅049⁆
//	⇔	\U				―	⁅158⁆
//	⇔	\V				―	⁅086⁆
//	⇔	\vb				―	⁅051⁆
//	⇔	\W				―	⁅085⁆
//	⇔	\X				―	⁅112⁆
//	⇔	\XOR				―	⁅072⁆
//	⇔	\Y				―	⁅001⁆⁅148⁆⁅155⁆
//	⇔	\Z				―	⁅082⁆
//	↔	ASCII code dependencies		―	⁅007⁆⁅010⁆
//	↔	bug, known			―	⁅066⁆
//	⇔	Cannot open index file		―	⁅162⁆
//	⇔	Cannot open section file	―	⁅174⁆
//	⇔	Control codes are forbidden...	―	⁅019⁆⁅023⁆
//	⇔	Control text didn't end		―	⁅022⁆
//	⇔	C text...didn't end		―	⁅126⁆
//	⇔	Double @ should be used...	―	⁅032⁆⁅065⁆
//	⇔	Extra } in comment		―	⁅037⁆
//	↔	high-bit character handling	―	⁅002⁆⁅003⁆⁅008⁆⁅038⁆⁅053⁆⁅067⁆⁅177⁆
//	⇔	Illegal control code...		―	⁅114⁆
//	⇔	Illegal use of @...		―	⁅036⁆
//	⇔	Improper format definition	―	⁅146⁆
//	⇔	Improper macro definition	―	⁅144⁆
//	⇔	Input ended in mid-comment	―	⁅033⁆
//	⇔	Input ended in middle of string	―	⁅014⁆
//	⇔	Input ended in section name	―	⁅017⁆
//	⇔	Irreducible scrap sequence...	―	⁅047⁆
//	⇔	Line had to be broken		―	⁅027⁆
//	⇔	Memory usage statistics:	―	⁅179⁆
//	⇔	Missing '|'...			―	⁅102⁆
//	⇔	Missing } in comment		―	⁅034⁆⁅035⁆
//	⇔	Missing left identifier...	―	⁅011⁆
//	⇔	Missing right identifier...	―	⁅012⁆
//	⇔	Never defined: <section name>	―	⁅025⁆
//	⇔	Never used: <section name>	―	⁅026⁆
//	↔	recursion			―	⁅004⁆⁅005⁆⁅106⁆
//	↔	reserved words			―	⁅009⁆
//	⇔	Section name didn't end		―	⁅018⁆
//	⇔	Section name too long		―	⁅020⁆
//	↔	special string characters	―	⁅048⁆
//	⇔	String didn't end		―	⁅013⁆
//	⇔	String too long			―	⁅015⁆
//	⇔	TeX string should be...		―	⁅141⁆
//	⇔	Tracing after...		―	⁅039⁆
//	⇔	UNKNOWN				―	⁅006⁆
//	⇔	Use @l in limbo...		―	⁅016⁆⁅024⁆
//	⇔	Verbatim string didn't end	―	⁅021⁆
//	⇔	Writing the index...		―	⁅161⁆
//	⇔	Writing the output file...	―	⁅138⁆
//	⇔	You can't do that...		―	⁅142⁆⁅150⁆
//	⇔	You need an = sign...		―	⁅147⁆
