// This program by D. E. Knuth is not copyrighted and can be used freely.
// Version 0 was released in December, 1981.
// Version 1 was released in September, 1982, with version 0 of TeX.
// Slight changes were made in October, 1982, for version 0.6 of TeX.
// Version 1.1 changed '_' to '\_' if not within an identifier (November, 1982).
// Version 1.2 added @= and @\ and marked changed modules (December, 1982).
// Version 1.3 marked and indexed changed modules better (January, 1983).
// Version 1.4 added "history" (February, 1983).
// Version 1.5 conformed to TeX version 0.96 (March, 1983).
// Version 1.6 conformed to TeX version 0.98 (May, 1983).
// Version 1.7 introduced the new change file format (June, 1983).
// Version 2 was released in July, 1983, with version 0.999 of TeX.
// Version 2.1 corrected a bug in changed_module reckoning (August, 1983).
// Version 2.2 corrected it better (August, 1983).
// Version 2.3 starts the output with \input webmac (August, 1983).
// Version 2.4 fixed a bug in compress(#) (September, 1983).
// Version 2.5 cleared xrefswitch after module names (November, 1983).
// Version 2.6 fixed a bug in declaration of trans array (January, 1984).
// Version 2.7 fixed a bug in real constants (August, 1984).
// Version 2.8 fixed a bug in change_buffer movement (August, 1985).
// Version 2.9 increased max_refs and max_toks to 30000 each (January, 1987).
// Version 3, for Sewell's book, fixed long-line bug in input_ln (March, 1989).
// Version 3.1 fixed a bug for programs with only one module (April, 1989).
// Version 4 was major change to allow 8-bit input (September, 1989).
// Version 4.1, for Breitenlohner, avoids English-only output (March, 1990).
// Version 4.2 conforms to ANSI standard for-loop rules (September, 1990).
// Version 4.3 catches extra } in input (Breitenlohner, September, 1991).
// Version 4.4 corrects changed_module logic, %-overflow (January, 1992).

// This program by D. E. Knuth is not copyrighted and can be used freely.
// Version 4.5, 2002/12.
#include <stdio.h>
#include <stdlib.h>
#include <setjmp.h>
#include <stdarg.h>

// ??1. Introduction.
// ???1.1:
// This program converts a ???WEB??? file to a ???TeX??? file.
// It was written by D. E. Knuth in October, 1981; a somewhat similar ???_ SAIL _??? program had been developed in March, 1979,
// although the earlier program used a top-down parsing method that is quite different from the present scheme.

// The code uses a few features of the local ???Pas??? compiler that may need to be changed in other installations:
// ??? 1)	Case statements have a default.
// ??? 2)	Input-output routines may need to be adapted for use with a particular character set and/or for printing messages on the user's terminal.
// These features are also present in the ???Pas??? version of ???TeX???, where they are used in a similar (but more complex) way.
// System-dependent portions of ???WEAVE??? can be identified by looking at the entries for ???system dependencies??? in the index below.
// (#) system dependencies

// The ???banner line??? defined here should be changed whenever ???WEAVE??? is modified.
#define banner "This is WEAVE, Version 4.4"

// 1.1???1.2:
// The program begins with a fairly normal header, made up of pieces that
// will mostly be filled in later.
// The ???WEB??? input comes from files web_file and change_file, and the ???TeX??? output goes to file tex_file.
// (#) system dependencies

// ???1.4: Compiler directives
// The ???Pas??? compiler used to develop this system has ???compiler directives??? that can appear in comments whose first character is a dollar sign.
// In production versions of ???WEAVE??? these directives tell the compiler that it is safe to avoid range checks
// and to leave out the extra code it inserts for the ???Pas??? debugger's benefit, although interrupts will occur if there is arithmetic overflow.
// (#) system dependencies
#if !DEBUG
#   pragma "C-,A+,D-"	// no range check, catch arithmetic overflow, no debug overhead
#else
#   pragma "C+,D+"	// but turn everything on when debugging
#endif // DEBUG
// 1.4???

// program WEAVE(web_file, change_file, tex_file);
// If it is necessary to abort the job because of a fatal error, the program calls the ???jump_out()??? procedure, which goes here.
// label end_of_WEAVE;	// go here to finish

// Constants.
// ???1.8: Constants in the outer block
// The following parameters are set big enough to handle ???TeX???, so they should be sufficient for most applications of ???WEAVE???.
const int max_bytes = 45000;	// 1/ww times the number of bytes in identifiers, index entries, and module names; must be less than 0x10000
const int max_names = 5000;	// number of identifiers, index entries, and module names; must be less than 0x2800
const int max_modules = 2000;	// greater than the total number of modules
const int hash_size = 353;	// should be prime
const int buf_size = 100;	// maximum length of input line
const int longest_name = 400;	// module names shouldn't be longer than this
const int long_buf_size = 500;	// buf_size + longest_name
const int line_length = 80;	// lines of ???TeX??? output have at most this many characters, should be less than 0x100
const int max_refs = 30000;	// number of cross references; must be less than 0x10000
const int max_toks = 30000;	// number of symbols in ???Pas??? texts being parsed; must be less than 0x10000
const int max_texts = 2000;	// number of phrases in ???Pas??? texts being parsed; must be less than 0x2800
const int max_scraps = 1000;	// number of tokens in ???Pas??? texts being parsed
const int stack_size = 200;	// number of simultaneous output levels
// 1.8???

// ???1.3:
// Some of this code is optional for use when debugging only; such material is conditioned on DEBUG.
// Other parts, conditioned on STATS, are optionally included if statistics about ???WEAVE???'s memory usage are desired.
#define DEBUG false	// change this to ????true???? when debugging
#define STATS false	// change this to ????true???? when gathering usage statistics
// 1.3???

// 1.2???1.5:
// Editor's Note:
// ???	Labels in C (unlike ??Pas??) are largely subsumed by the ????break????, ????continue???? and ????return???? statements in C,
//	and are self-declaring, so that declarations of them are not required here.
// ???	The generic labels still used are for:
//	???	????restart????	// for the very beginning of a procedure
//	???	????reswitch????	// for the top of a ????switch???? statement that is being used as a finite-state control
//	???	????found????	// for jumps out of successful search loops

// 1.5???1.6:
// Update-assignments, which are present in C, were defined as macros for ??Pas??, and are therefore no longer needed or used.
// The following update-assignments are used; ???X, ???X, X???, X???, X += Y, X -= Y, X *= Y, X /= Y, X %= Y.

// 1.6???1.7:
// The syntax of ????switch???? statements, particularly ????default???? cases, which are present in C, was not uniform in ??Pas??.
// The macros defined to remedy this are no longer needed or used.
// Editor's Note:
// ???	This is all subsumed by the syntax for switch statements in C.

// 1.7???1.9: Globals in the outer block (1/34)
// A global variable called history will contain one of four values at the end of every run:
// ???	spotless means that no unusual messages were printed;
// ???	harmless_message means that a message of possible interest was printed but no serious errors were detected;\
// ???	error_message means that at least one error was found;
// ???	fatal_message means that the program terminated abnormally.
// The value of history does not influence the behavior of the program;
// it is simply computed for the convenience of systems that might want to use such information.
// ???1.10: Set initial values (1/20)
enum {
   spotless = 0,		// history value for normal jobs
   harmless_message = 1,	// history value when non-serious info was printed
   error_message = 2,		// history value when an error was noted
   fatal_message = 3		// history value when we had to stop prematurely
} history ??? spotless;		// how bad was this run?
// 1.10???

inline void mark_harmless(void) { if (history ??? spotless) history ??? harmless_message; }
inline void mark_error(void) { history ??? error_message; }
inline void mark_fatal(void) { history ??? fatal_message; }
// 1.9???

// ??2. The Character Set.
// ???2.1: Types in the outer block (1/7)
// One of the main goals in the design of ???WEB??? has been to make it readily portable between a wide variety of computers.
// Yet ???WEB??? by its very nature must use a greater variety of characters than most computer programs deal with,
// and character encoding is one of the areas in which existing machines differ most widely from each other.
//
// To resolve this problem, all input to ???WEAVE??? and ???TANGLE??? is converted to an internal eight-bit code that is essentially standard ASCII,
// the ???American Standard Code for Information Interchange.???
// The conversion is done immediately when each character is read in.
// Conversely, characters are converted from ASCII to the user's external representation just before they are output.
// (The original ASCII code was seven bits only; ???WEB??? now allows eight bits in an attempt to keep up with modern times.)
//
// Such an internal code is relevant to users of ???WEB??? only because it is the code used for preprocessed constants like ???'A'???.
// If you are writing a program in ???WEB??? that makes use of such one-character constants,
// you should convert your input to ASCII form, like ???WEAVE??? and ???TANGLE??? do.
// Otherwise ???WEB???'s internal coding scheme does not affect you.
//
// Here is a table of the standard visible ASCII codes:
//	xy ??? x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xa xb xc xd xe xf
//	????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????
//	2y ???     !  "  #  $  %  &  '  (  )  *  +  ,  -  .  /
//	3y ???  0  1  2  3  4  5  6  7  8  9  :  ;  <  =  >  ?
//	4y ???  @  A  B  C  D  E  F  G  H  I  J  K  L  M  N  O
//	5y ???  P  Q  R  S  T  U  V  W  X  Y  Z  [  \  ]  ^  _
//	6y ???  `  a  b  c  d  e  f  g  h  i  j  k  l  m  n  o
//	7y ???  p  q  r  s  t  u  v  w  x  y  z  {  |  }  ~
// (Actually, of course, code 0x20 is an invisible blank space.)
// Code 0x5e was once an upward arrow (???^K???), and code 0x5f was once a left arrow (???^X???), in olden times when the first draft of ASCII code was prepared;
// but ???WEB??? works with today's standard ASCII in which those codes represent circumflex and underline as shown.
typedef enum {0x100} ASCII_code;	// eight-bit numbers, a subrange of the integers

// 2.1???2.2: Types in the outer block (2/7)
// The original ???Pas??? compiler was designed in the late 1960s, when six-bit character sets were common, so it did not make provision for lowercase letters.
// Nowadays, of course, we need to deal with both capital and small letters in a convenient way,
// so ???WEB??? assumes that it is being used with a ???Pas??? whose character set contains at least the characters of standard ASCII as listed above.
// Some ???Pas??? compilers use the original name char for the data type associated with the characters in text files,
// while other ???Pas???s consider char to be a 64-element subrange of a larger data type that has some other name.
//
// In order to accommodate this difference, we shall use the name text_char to stand for the data type of the characters in the input and output files.
// We shall also assume that text_char consists of the elements chr(first_text_char) through chr(last_text_char), inclusive.
// The following definitions should be adjusted if necessary.
// (#) system dependencies
typedef char text_char char;	// the data type of characters in text files
#define first_text_char 0x00	// ordinal number of the smallest element of text_char
#define last_text_char 0xff	// ordinal number of the largest element of text_char

// typedef file(text_char) text_file;
typedef FILE *text_file;

// 2.2???2.3: Globals in the outer block (2/34)
// The ???WEAVE??? and ???TANGLE??? processors convert between ASCII code and the user's external character set
// by means of xord[] and xchr[] that are analogous to ???Pas???'s ord() and chr().
ASCII_code xord[text_char];	// specifies conversion of input characters
text_char xchr[ASCII_code] ??? {	// specifies conversion of output characters
// ???2.7: Set initial values (3/20) (0x01-0x1f, 0x80-0xff).
   "        "  "        "	// 00-07, 08-0f
   "        "  "        "	// 10-17, 18-1f
// ???2.4: Set initial values (2/20)
// If we assume that every system using ???WEB??? is able to read and write the visible characters of standard ASCII
// (although not necessarily using the ASCII codes to represent them),
// the following assignment statements initialize most of the xchr[] properly, without needing any system-dependent changes.
// For example, the statement ???xchr[0101] ??? 'A'??? that appears in the present ???WEB??? file
// might be encoded in, say, ???_ EBCDIC _??? code on the external medium on which it resides,
// but ???TANGLE??? will convert from this external code to ASCII and back again.
// Therefore the assignment statement ???xchr[65] ??? 'A'??? will appear in the corresponding ???Pas??? file,
// and ???Pas??? will compile this statement so that xchr[65] receives the character ???A??? in the external (char) code.
   " !\"#$%&'" "()*+,-./"	// 20-27, 28-2f
   "01234567"  "89:;<=>?"	// 30-37, 38-3f
   "@ABCDEFG"  "HIJKLMNO"	// 40-47, 48-4f
   "PQRSTUVW"  "XYZ[\\]^_"	// 50-57, 58-5f
   "`abcdefg"  "hijklmno"	// 60-67, 68-6f
   "pqrstuvw"  "xyz{|}~ "	// 70-77, 78-7f // The ASCII codes 0x00 (above) and 0x7f are not used.
// 2.4???
// Here now is the system-dependent part of the character set.
// If ???WEB??? is being implemented on a garden-variety ???Pas??? for which only standard ASCII codes will appear in the input and output files,
// you don't need to make any changes here.
// But if you have, for example, an extended character set like the one in Appendix C of ???_ The ???TeX??? book _???,
// the initialization for 0x01-0x1f  should be changed to
//	for (enum {0x100} i ??? 0x01 ??? 0x1f) xchr[i] ??? chr(i);
// ???WEB???'s character set is essentially identical to ???TeX???'s, even with respect to characters less than 0x20.
// (#) system dependencies
//
// Changes to the present module will make ???WEB??? more friendly on computers that have an extended character set,
// so that one can type things like ???^Z??? instead of ?????????.
// If you have an extended set of characters that are easily incorporated into text files,
// you can assign codes arbitrarily here, giving an xchr equivalent to whatever characters the users of ???WEB??? are allowed to have in their input files,
// provided that unsuitable characters do not correspond to special codes like carriage_return that are listed above.
//
// (The present file ???WEAVE.WEB??? does not contain any of the non-ASCII characters, because it is intended to be used with all implementations of ???WEB???.
// It was originally created on a Stanford system that has a convenient extended character set,
// then ???sanitized??? by applying another program that transliterated all of the non-standard characters into standard equivalents.)
   "        "  "        "	// 80-87, 88-8f
   "        "  "        "	// 90-97, 98-9f
   "        "  "        "	// a0-a7, a8-af
   "        "  "        "	// b0-b7, b8-bf
   "        "  "        "	// c0-c7, c8-cf
   "        "  "        "	// d0-d7, d8-df
   "        "  "        "	// e0-e7, e8-ef
   "        "  "        "	// f0-f7, f8-ff
// 2.7???
};

// 2.3???2.5:
// Some of the ASCII codes below 0x20 have been given symbolic names in ???WEAVE??? and ???TANGLE??? because they are used with a special meaning.
#define and_sign		0x04	// equivalent to ???????????????
#define not_sign		0x05	// equivalent to ??????????????
#define set_element_sign	0x06	// equivalent to ???????????????
#define tab_mark		0x09	// equivalent to ???\t???
#define line_feed		0x0a	// equivalent to ???\n???
#define form_feed		0x0c	// equivalent to ???\f???
#define carriage_return		0x0d	// equivalent to ???\r???
#define left_arrow		0x18	// equivalent to ???????????????
#define not_equal		0x1a	// equivalent to ???????????????
#define less_or_equal		0x1c	// equivalent to ???????????????
#define greater_or_equal	0x1d	// equivalent to ???????????????
#define equivalence_sign	0x1e	// equivalent to ???????????????
#define or_sign			0x1f	// equivalent to ???????????????
// 2.5???

// ??3. Input and Output.
// ???3.1:
// The input conventions of this program are intended to be very much like those of ???TeX???
// (except, of course, that they are much simpler, because much less needs to be done).
// Furthermore they are identical to those of ???TANGLE???.
// Therefore people who need to make modifications to all three systems should be able to do so without too many headaches.
//
// We use the standard ???Pas??? input/output procedures in several places that ???TeX??? cannot,
// since ???WEAVE??? does not have to deal with files that are named dynamically by the user, and since there is no input from the terminal.

// 3.1???3.2: Globals in the outer block (3/34)
// Terminal output is done by writing on file term_out, which is assumed to consist of characters of type text_char:
// (#) system dependencies
// Editor's Note:
// ???	The original print_ln(A, ...), new_line() and print_nl(A, ...)
//	are subsumed respectively by print(A "\n", ...), print("\n") and print("\n" A, ...)
// ???	The original rewrite(A, ...) is subsumed by fopen()
// ???	The original update_terminal(A, ...) is subsumed by fflush()
text_file term_out;	// the terminal as an output file

inline void print(char *A, ...) { fprintf(term_out, A, ...); }	// ???print??? means write on the terminal
inline void write(text_file F, char *A, ...) { fprintf(F, A, ...); }
#define rewrite(F) (F = fopen(F##_name, "wa"))

// 3.2???3.4:
// The update_terminal() procedure is called when we want to make sure
// that everything we have output to the terminal so far has actually left the computer's internal buffers and been sent.
// (#) system dependencies
#define update_terminal() fflush(term_out)	// empty the terminal output buffer

// 3.4???3.5: Globals in the outer block (4/34)
// The main input comes from web_file; this input may be overridden by changes in change_file.
// (If change_file is empty, there are no changes.)
text_file web_file;	// primary input
text_file change_file;	// updates

// 3.5???3.6:
// The following code opens the input files.
// Since these files were listed in the program header, we assume that the ???Pas??? runtime system has already checked that suitable file names have been given;
// therefore no additional error checking needs to be done.
// We will see below that ???WEAVE??? reads through the entire input twice.
// (#) system dependencies

// Editor's Note:
// ???	The original eof(f), eoln(f), f^ are subsumed respectively by next(f) ??? EOF, next(f) ??? '\n', next(f).
// ???	The original read_ln(f) is only used when eoln(f) is true, so it is subsumed by get(f).
// ???	reset(f) should open up a file for input and buffer 1 character (or EOF, if the file is empty or fails to open).
// ???	get(f) should buffer the next character (or EOF, if the file is at its end).
// ???	next(f) is the character Next_##f in the buffer, itself, if f is opened for reading or EOF if f ??? NULL or f is not open for reading.
#define get(f) (Next_##f ??? f ??? NULL? EOF: fgetc(f))
#define reset(f) (f ??? fopen(f##_name, "ra"), get(f))
#define next(f) Next_##f

void open_input(void) {	// prepare to read web_file and change_file
   reset(web_file), reset(change_file);
}

// 3.6???3.7: Globals in the outer block (5/34)
// The main output goes to tex_file.
text_file tex_file;

// 3.7???3.9: Globals in the outer block (6/34)
// Input goes into an array called buffer.
ASCII_code buffer[0..long_buf_size];

// 3.9???3.10:
// The input_ln() procedure brings the next line of input from the specified file into the buffer array and returns the value true,
// unless the file has already been entirely read, in which case it returns false.
// The conventions of ???TeX??? are followed;
// i.e., ASCII_code numbers representing the next line of the file are input into buffer[0], buffer[1], ???, buffer[limit - 1];
// trailing blanks are ignored; and the global variable limit is set to the length of the line.
// (#) system dependencies
// The value of limit must be strictly less than buf_size.
//
// We assume that none of the ASCII_code values of buffer[j] for 0 ??? j < limit is equal to 0, 0x7f, line_feed, form_feed, or carriage_return.
// Since buf_size is strictly less than long_buf_size,
// some of ???WEAVE???'s routines use the fact that it is safe to refer to buffer[limit + 2] without overstepping the bounds of the array.
bool input_ln(text_file &f) {	// inputs a line or returns false
   limit ??? 0;
   enum {0..buf_size} final_limit ??? 0;	// limit without trailing blanks
   if (next(f) ??? EOF) return false
   while (next(f) ??? '\n') {
      buffer[limit] ??? xord[next(f)], get(f);
      if (buffer[limit???] ??? ' ') final_limit ??? limit;
      if (limit ??? buf_size) {
         while (next(f) ??? '\n') get(f);
         limit???;	// keep buffer[buf_size] empty
         if (final_limit > limit) final_limit ??? limit;
         print("\n! Input line too long"), loc ??? 0, error();

      }
   }
   get(f), limit ??? final_limit; return true;
}

// ??4. Reporting Errors to the User.
// ???4.1: Globals in the outer block (7/34)
// The ???WEAVE??? processor operates in three phases:
// ???	first it inputs the source file and stores cross-reference data,
// ???	then it inputs the source once again and produces the ???TeX??? output file, and finally it sorts and outputs the index.
// The global variables phase_one and phase_three tell which Phase we are in.
bool phase_one;		// true in Phase I, false in Phases II and III
bool phase_three;	// true in Phase III, false in Phases I and II
// 4.1???

// ???1.2: [continued]
// ???4.2: Error handling procedures (1/3)
// If an error is detected while we are debugging, we usually want to look at the contents of memory.
// A special procedure will be declared later for this purpose.
#if DEBUG
void debug_help(void);
#endif // DEBUG

// 4.2???4.3: Error handling procedures (2/3)
// The command ???err_print("! Error message")' will report a syntax error to the user,
// by printing the error message at the beginning of a new line and then giving an indication of where the error was spotted in the source file.
// Note that no period follows the error message, since the error routine will automatically supply a period.
//
// The actual error indications are provided by a procedure called error().
// However, error messages are not actually reported during phase one, since errors detected on the first pass will be detected again during the second.
void error(void) {	// prints ??????.?????? and location of error message
// ???4.4: Print error location based on input buffer
// The error locations can be indicated by using the global variables loc, line, and changing,
// which tell respectively the first unlooked-at position in buffer, the current line number,
// and whether or not the current line is from change_file or web_file.
// This routine should be modified on systems whose standard text editor has special line-numbering conventions.
// (#) system dependencies
   print(". (%sl.%1d)\n", changing? "change file ": "", line);
   enum {0..long_buf_size} l ??? loc ??? limit? limit: loc;	// index into buffer
   for (enum {0..long_buf_size} k ??? l) printf("%c", buffer[k] ??? tab_mark? ' ': xchr[buffer[k]]);	// print the characters already read
   print("\n");
   for (k ??? l) print(" ");	// space out the next line
   for (k ??? l ??? limit - 1) print("%c", xchr[buffer[k]]);	// print the part not yet read
   if (buffer[limit] ??? '|') print("%c", xchr['|']);	// end of ???Pas??? text in module names
   print(" ");	// this space separates the message from future asterisks
// 4.4???
   update_terminal(), mark_error();
#if DEBUG
   debug_skipped ??? debug_cycle, debug_help();
#endif // DEBUG
}

inline void err_print(char *A, ...) {
   if (!phase_one) print("\n" A, ...), error();
}

// 4.3???4.5: Error handling procedures (3/3)
// The jump_out() procedure just cuts across all active procedure levels and jumps out of the program.
// This is the only non-local ????goto???? statement in ???WEAVE???.
// It is used when no recovery from a particular error has been provided.
//
// Some ???Pas??? compilers do not implement non-local goto statements.
// (#) system dependencies
// In such cases the code that appears at label end_of_WEAVE should be copied into the jump_out() procedure,
// followed by a call to a system procedure that terminates the program.
#define fatal_error(A) (print("\n" A), error(), mark_fatal(), jump_out())

void jump_out(void) {
   goto end_of_WEAVE;
}
// 4.5???
// 1.2???

// ???4.6:
// Sometimes the program's behavior is far different from what it should be,
// and ???WEAVE??? prints an error message that is really for the ???WEAVE??? maintenance person, not the user.
// In such cases the program says confusion("indication of where we are").
// Editor's Note:
// ???	confusion(A) is not used anywhere.
// #define confusion(A) fatal_error("! This can't happen (",A, ")")

// 4.6???4.7:
// An overflow stop occurs if ???WEAVE???"s tables aren"t large enough.
#define overflow(A) fatal_error("! Sorry, " A " capacity exceeded")
// 4.7???

// ??5. Data Structures.
// ???5.1: Types in the outer block (3/7)
// During the first phase of its processing, ???WEAVE??? puts identifier names, index entries,
// and module names into the large byte_mem[] array, which is packed with eight-bit integers.
// Allocation is sequential, since names are never deleted.
//
// An auxiliary array byte_start[] is used as a directory for byte_mem[], and the link[], ilk[], and xref[] arrays give further information about names.
// These auxiliary arrays consist of sixteen-bit items.
typedef enum {0x100} eight_bits;	// unsigned one-byte quantity
typedef enum {0x10000} sixteen_bits;	// unsigned two-byte quantity
// 5.1???5.2: Globals in the outer block (8/34)
// ???WEAVE??? has been designed to avoid the need for indices that are more than sixteen bits wide, so that it can be used on most computers.
// But there are programs that need more than 0x10000 bytes; ???TeX??? is one of these.
// To get around this problem, a slight complication has been added to the data structures:
// byte_mem[] is a two-dimensional array, whose first index is either 0 or 1.
// (For generality, the first index is actually allowed to run between 0 and ww - 1, where ww is defined to be 2;
// the program will work for any positive value of ww, and it can be simplified in obvious ways if ww ??? 1.)

#define ww 2	// we multiply the byte capacity by approximately this amount

ASCII_code byte_mem[ww][0..max_bytes];	// characters of names
// ???5.6: Set initial values (7/20)
// The extra 0 makes name 0 of length zero
sixteen_bits byte_start[0..max_names] ??? { 0, 0, 0 };	// directory into byte_mem[]
// 5.6???
sixteen_bits link[0..max_names];	// hash table or tree links
// ???5.8: Set initial values (8/20)
//   root ??? 0;	// the binary search tree starts out with nothing in it
sixteen_bits ilk[0..max_names] ??? { 0 };	// type codes or tree links
// 5.8???5.14: Set initial values (9/20)
//   xref[0] ??? 0;	// cross references to undefined modules
sixteen_bits xref[0..max_names] ??? { 0 };	// heads of cross-reference lists
// 5.14???

// 5.2???5.3: Types in the outer block (4/7)
// The names of identifiers are found by computing a hash address h
// and then looking at strings of bytes signified by hash[h], link[hash[h]], link[link[hash[h]]], ???,
// until either finding the desired name or encountering a zero.
//
// A ???name_pointer??? variable, which signifies a name, is an index into byte_start[].
// The actual sequence of characters in the name pointed to by p appears in positions byte_start[p] to byte_start[p + ww] - 1, inclusive,
// in the segment of byte_mem[] whose first index is p%ww.
// Thus, when ww ??? 2 the even-numbered name bytes appear in byte_mem[0][] and the odd-numbered ones appear in byte_mem[1][].
// The pointer 0 is used for undefined module names; we don't want to use it for the names of identifiers,
// since 0 stands for a null pointer in a linked list.
//
// We usually have byte_start[name_ptr + w] ??? byte_ptr[(name_ptr + w)%ww] for 0 ??? w < ww,
// since these are the starting positions for the next ww names to be stored in byte_mem[].
#define length(A) (byte_start[A + ww] - byte_start[A])	// the length of a name

typedef enum {0..max_names} name_pointer;	// identifies a name

// 5.3???5.4: Globals in the outer block (9/34)
// ???5.6: Set initial values (7/20) [continued]
name_pointer name_ptr ??? 1;	// first unused position in byte_start[]
enum {0..max_bytes} byte_ptr[ww] ??? {0, 0};	// first unused position in byte_mem[]
// 5.6???

// 5.4???5.7:
// Several types of identifiers are distinguished by their ilk:
// ???	normal identifiers are part of the ???Pas??? program and will appear in italic type.
// ???	roman identifiers are index entries that appear after ???@^??? in the ???WEB??? file.
// ???	wildcard identifiers are index entries that appear after ???@:??? in the ???WEB??? file.
// ???	typewriter identifiers are index entries that appear after ???@.??? in the ???WEB??? file.
// ???	array_like, begin_like, ???, var_like identifiers are ???Pas??? reserved words
//	whose ilk explains how they are to be treated when ???Pas??? code is being formatted.
// ???	Finally, if c is an ASCII code, an ilk equal to char_like + c denotes a reserved word that will be converted to character c.

// Editor's Note:
// ???	The enum type IdClass has been added to the original.
typedef enum {
   normal = 0,		// ordinary identifiers have normal ilk
   roman = 1,		// normal index entries have roman ilk
   wildcard = 2,	// user-formatted index entries have wildcard ilk
   typewriter = 3,	// ???typewriter type??? entries have typewriter ilk
   array_like = 4,	// ????array????, ????file????, ????set????
   begin_like = 5,	// ????begin????
   case_like = 6,	// ????case????
   const_like = 7,	// ????const????, ????label????, ????type????
   div_like = 8,	// ????div????, ????mod????
   do_like = 9,		// ????do????, ????of????, ????then????
   else_like = 10,	// ?? else????
   end_like = 11,	// ????end????
   for_like = 12,	// ????for????, ????while????, ????with????
   goto_like = 13,	// ????goto????, ????packed????
   if_like = 14,	// ????if????
   in_like = 15,	// ????in????
   nil_like = 16,	// ????nil????
   proc_like = 17,	// ????function????, ????procedure????, ????program????
   record_like = 18,	// ????record????
   repeat_like = 19,	// ????repeat????
   to_like = 20,	// ????downto????, ????to????
   until_like = 21,	// ????until????
   var_like = 22,	// ????var????
   loop_like = 23,	// ????loop????, ????xclause????
   char_like = 24,	// ????and????, ????or????, ????not????, ????in????
} IdClass;
#define reserved(A)	(ilk[A] > typewriter)	// tells if a name is a reserved word
#define char_like(Ch)	(char_like + (Ch))	// a reserved word that will be converted to character Ch.

// 5.7???5.8: Set initial values (8/20)
// The names of modules are stored in byte_mem[] together with the identifier names,
// but a hash table is not used for them because ???WEAVE??? needs to be able to recognize a module name when given a prefix of that name.
// A conventional binary seach tree is used to retrieve module names, with fields called llink and rlink in place of link and ilk.
// The root of this tree is rlink[0].
#define llink link	// left link in binary search tree for module names
#define rlink ilk	// right link in binary search tree for module names
#define root rlink[0]	// the root of the binary search tree for module names
// sixteen_bits root ??? 0;

// 5.8???5.9:
// Here is a little procedure that prints the text of a given name on the user's terminal.
void print_id(name_pointer p) {	// print identifier or module name
   if (p ??? name_ptr) print("IMPOSSIBLE");
   else {
      enum {ww} w ??? p%ww;	// row of byte_mem[]
      for (enum {0..max_bytes} k ??? byte_start[p] ??? byte_start[p + ww] - 1) print("%c", xchr[byte_mem[w][k]]);
   }
}

// 5.9???5.10: Globals in the outer block (10/34)
// We keep track of the current module number in module_count, which is the total number of modules that have started.
// Modules which have been altered by a change file entry have their changed_module flag turned on during the first phase.
enum {0..max_modules} module_count;	// the current module number
bool changed_module[0..max_modules];	// is it changed?
bool change_exists;			// has any module changed?

// 5.10???5.11:
// The other large memory area in ???WEAVE??? keeps the cross-reference data.
// All uses of the name p are recorded in a linked list beginning at xref[p], which points into the xmem array.
// Entries in xmem consist of two sixteen-bit items per word, called the num and xlink fields.
// If x is an index into xmem, reached from name p, the value of num(x) is either a module number where p is used,
// or it is def_flag plus a module number where p is defined; and xlink(x) points to the next such cross reference for p, if any.
// This list of cross references is in decreasing order by module number.
// The current number of cross references is xref_ptr.
//
// The global variable xref_switch is set either to def_flag or to zero,
// depending on whether the next cross reference to an identifier is to be underlined or not in the index.
// This switch is set to def_flag when ???@!??? or ???@d??? or ???@f??? is scanned,
// and it is cleared to zero when the next identifier or index entry cross reference has been made.
// Similarly, the global variable mod_xref_switch is either def_flag or zero, depending on whether a module name is being defined or used.
#define num(A)		xmem[A].num_field
#define xlink(A)	xmem[A].xlink_field
#define def_flag	0x2800	// must be strictly larger than max_modules

// 5.11???5.12: Types in the outer block (5/7)
typedef enum {0..max_refs} xref_number;

// 5.12???5.13: Globals in the outer block (11/34)
// ???5.14: Set initial values (9/20) [continued]
struct {
   sixteen_bits num_field;	// module number plus zero or def_flag
   sixteen_bits xlink_field;	// pointer to the previous cross reference
} xmem[xref_number] ??? { { .num_field: 0 }};
xref_number xref_ptr ??? 0;	// the largest occupied position in xmem
enum {0..def_flag} xref_switch ??? 0, mod_xref_switch ??? 0;	// either zero or def_flag
// 5.14???

// 5.13???5.15:
// A new cross reference for an identifier is formed by calling new_xref(),
// which discards duplicate entries and ignores non-underlined references to one-letter identifiers or ???Pas??? 's reserved words.
inline void append_xref(sixteen_bits A) { if (xref_ptr ??? max_refs) overflow("cross reference"); else num(???xref_ptr) ??? A; }

void new_xref(name_pointer p) {
   if ((reserved(p) || byte_start[p] + 1 ??? byte_start[p + ww]) && xref_switch ??? 0) return;
   sixteen_bits m ??? module_count + xref_switch;	// new cross-reference value
   xref_switch ??? 0;
   xref_number q ??? xref[p];	// pointer to previous cross reference
   if (q > 0) {
      sixteen_bits n ??? num(q);	// previous cross-reference value
      if (n ??? m || n ??? m + def_flag) return;
      else if (m ??? n + def_flag) { num(q) ??? m; return; }
   }
   append_xref(m), xlink(xref_ptr) ??? q, xref[p] ??? xref_ptr;
}

// 5.15???5.16:
// The cross reference lists for module names are slightly different.
// Suppose that a module name is defined in modules $m_1$, ???, $m_k$ and used in modules n_1, ???, n_l.
// Then its list will contain m_1 + def_flag, m_k + def_flag, ???, m_2 + def_flag, n_l, ???, n_1, in this order.
// After Phase II, however, the order will be m_1 + def_flag, ???, m_k + def_flag, n_1, ???, n_l.
void new_mod_xref(name_pointer p) {
   xref_number q ??? xref[p], r ??? 0;	// pointers to previous cross references
   if (q > 0) {
      if (mod_xref_switch ??? 0) while (num(q) ??? def_flag) r ??? q, q ??? xlink(q);
      else if (num(q) ??? def_flag) r ??? q, q ??? xlink(q);
   }
   append_xref(module_count + mod_xref_switch), xlink(xref_ptr) ??? q;
   mod_xref_switch ??? 0;
   if (r ??? 0) xref[p] ??? xref_ptr; else xlink(r) ??? xref_ptr;
}

// 5.16???5.17: Types in the outer block (6/7)
// A third large area of memory is used for sixteen-bit ???tokens???, which appear in short lists similar to the strings of characters in byte_mem[].
// Token lists are used to contain the result of ???Pas??? code translated into ???TeX??? form;
// further details about them will be explained later.
// A text_pointer variable is an index into tok_start.
typedef enum {0..max_texts} text_pointer;	// identifies a token list

// 5.17???5.18: Globals in the outer block (12/34)
// The first position of tok_mem that is unoccupied by replacement text is called tok_ptr, and the first unused location of tok_start is called text_ptr.
// Thus, we usually have tok_start[text_ptr] ??? tok_ptr.
sixteen_bits tok_mem[0..max_toks];	// tokens
// ???5.19: Set initial values (10/20)
sixteen_bits tok_start[text_pointer] ??? {1, 1};	// directory into tok_mem
text_pointer text_ptr ??? 1;		// first unused position in tok_start
enum {0..max_toks} tok_ptr ??? 1;		// first unused position in tok_mem
#if STATS
enum {0..max_toks} max_tok_ptr ??? 1, max_txt_ptr ??? 1;	// largest values occurring
#endif // STATS
// 5.19???
// 5.18???

// ??6. Searching for Identifiers.
// ???6.1: Globals in the outer block (13/34)
// The hash table described above is updated by the id_lookup() procedure, which finds a given identifier and returns a pointer to its index in byte_start[].
// The identifier is supposed to match character by character and it is also supposed to have a given ilk code;
// the same name may be present more than once if it is supposed to appear in the index with different typesetting conventions.
// If the identifier was not already present, it is inserted into the table.

// Because of the way ???WEAVE???'s scanning mechanism works,
// it is most convenient to let id_lookup() search for an identifier that is present in the buffer array.
// Two other global variables specify its position in the buffer: the first character is buffer[id_first], and the last is buffer[id_loc - 1].
enum {0..long_buf_size} id_first;	// where the current identifier begins in the buffer
enum {0..long_buf_size} id_loc;		// just after the current identifier in the buffer

// ???6.2: Local variables for initialization (3/4)
// Initially all the hash lists are empty.
// 6.2???
sixteen_bits hash[0..hash_size];	// heads of hash lists
// ???6.3: Set initial values (11/20)
// for (enum {0..hash_size} h ??? hash_size) hash[h] ??? 0;
// 6.3???

// 6.1???6.4:
// Here now is the main procedure for finding identifiers (and index entries).
// The parameter t is set to the desired ilk code.
// The identifier must either have ilk ??? t, or we must have t ??? normal and the identifier must be a reserved word.
name_pointer id_lookup(eight_bits t) {	// finds current identifier
   enum {0..long_buf_size} l ??? id_loc-id_first;	// compute the length of the given identifier
// ???6.5: Compute the hash code h
// A simple hash code is used: If the sequence of ASCII codes is c_1 c_2 ??? c_m, its hash value will be
//	(2???????? c_1 + 2???????? c_2 + ??? + c_n) % hash_size.
   enum {0..hash_size} h ??? buffer[id_first];	// hash code
   for (enum {0..long_buf_size} i ??? id_first + 1; i < id_loc; i???) h ??? (h + h + buffer[i])%hash_size;
// 6.5???6.6: Compute the name location p from h
// If the identifier is new, it will be placed in position p ??? name_ptr, otherwise p will point to its existing location.
   name_pointer p ??? hash[h];	// where the identifier is being sought
   for (; p ??? 0; p ??? link[p]) {
      if (length(p) ??? l && (ilk[p] ??? t || t ??? normal && reserved(p)))
   // ???6.7: Compare name p with current identifier, break if equal
      enum {0..long_buf_size} i ??? id_first;	// index into buffer
      enum {0..max_bytes} k ??? byte_start[p];	// index into byte_mem[]
      enum {ww} w ??? p%ww;			// row of byte_mem[]
      for (; i < id_loc && buffer[i] ??? byte_mem[w][k]; i???, k???);
      if (i ??? id_loc) break;	// all characters agree
   // 6.7???
   }
   if (p ??? 0) {
      p ??? name_ptr;	// the current identifier is new
      link[p] ??? hash[h], hash[h] ??? p;	// insert p at beginning of hash list
   }
// 6.6???
   if (p ??? name_ptr) {
   // ???6.8: Enter a new name into the table at position p
   // When we begin the following segment of the program, p ??? name_ptr.
      enum {ww} w ??? name_ptr%ww;	// row of byte_mem[]
      if (byte_ptr[w] + l > max_bytes) overflow("byte memory");
      if (name_ptr + ww > max_names) overflow("name");
      enum {0..max_bytes} k ??? byte_ptr[w];	// get ready to move the identifier into byte_mem[]
      for (enum {0..long_buf_size} i ??? id_first; i < id_loc; k???, i???) byte_mem[w][k] ??? buffer[i];
      byte_start[name_ptr??? + ww] ??? byte_ptr[w] ??? k;
      ilk[p] ??? t, xref[p] ??? 0;
   // 6.8???
   }
   return p;
}
// 6.4???

// ??7. Initializing the Table of Reserved Words.
// ???7.1: Globals in the outer block (14/34)
// We have to get ???Pas??? 's reserved words into the hash table, and the simplest way to do this is to insert them every time ???WEAVE??? is run.
// A few macros permit us to do the initialization with a compact program.
name_pointer cur_name;	// points to the identifier just inserted

inline void id(int N, char *S, IdClass T) {
   id_first ??? 10 - N;
   for (n ??? N) buffer[id_first + n] ??? S[n];
   cur_name ??? id_lookup(T)
}
// 7.1???

// ??8. Searching for Module Names.
// ???8.1: Globals in the outer block (15/34)
// The mod_lookup() procedure finds the module name mod_text[1..l] in the search tree,
// after inserting it if necessary, and returns a pointer to where it was found.

// ???10.10: Set initial values (13/20)
// Module names are placed into the mod_text array with consecutive spaces, tabs, and carriage-returns replaced by single spaces.
// There will be no spaces at the beginning or the end.
// (We set mod_text[0] ??? ' ' to facilitate this, since the mod_lookup() routine uses mod_text[1] as the first character of the name.)
ASCII_code mod_text[0..longest_name] ??? " ";	// name being sought for
// 10.10???

// 8.1???8.2:
// According to the rules of ???WEB???, no module name should be a proper prefix of another,
// so a ???clean??? comparison should occur between any two names.
// The result of mod_lookup() is 0 if this prefix condition is violated.
// An error message is printed when such violations are detected during phase two of ???WEAVE???.

// Editor's Note:
// ???	The enum type ModDiffT has been added to the original.
typedef enum {
   less = 0,		// the first name is lexicographically less than the second
   equal = 1,		// the first name is equal to the second
   greater = 2,		// the first name is lexicographically greater than the second
   prefix = 3,		// the first name is a proper prefix of the second
   extension = 4	// the first name is a proper extension of the second
} ModDiffT;

name_pointer mod_lookup(sixteen_bits l) {	// finds module name
   ModDiffT c ??? greater;	// comparison between two names
   name_pointer q ??? 0;		// father of node p
   for (name_pointer p ??? root; p ??? 0; ) {
      ModDiffT c ??? MatchNames(p, l);
      q ??? p;
      if (c ??? less) p ??? llink[q];
      else if (c ??? greater) p ??? rlink[q];
      else if (c ??? equal) return p;
      else { err_print("! Incompatible section names"); return 0; }
   }
// ???8.3: Enter a new module name into the tree
   enum {ww} w ??? name_ptr%ww;		// row of byte_mem[]
   enum {0..max_bytes} k ??? byte_ptr[w];	// index into byte_mem[]
   if (k + l > max_bytes) overflow("byte memory");
   if (name_ptr > max_names - ww) overflow("name");
   name_pointer p ??? name_ptr;
   if (c ??? less) llink[q] ??? p; else rlink[q] ??? p;
   rlink[p] ??? llink[p] ??? 0, xref[p] ??? 0;
   for (enum {0..longest_name} j ??? 1 ??? l) byte_mem[w][k + j - 1] ??? mod_text[j];	// index into mod_text
   byte_start[name_ptr??? + ww] ??? byte_ptr[w] ??? k + l;
   return p;
}

// 8.2???8.4: Set variable c to the result of comparing the given name to name p
inline ModDiffT MatchNames(name_pointer p, sixteen_bits l) {
   enum {0..max_bytes} k ??? byte_start[p];	// index into byte_mem[]
   enum {ww} w ??? p%ww;				// row of byte_mem[]
   enum {0..longest_name} j ??? 1;		// index into mod_text
   for (; k < byte_start[p + ww] && j ??? l && mod_text[j] ??? byte_mem[w][k]; k???, j???);
   return
      k ??? byte_start[p + ww]? (j > l? equal: extension):
      j > l? prefix: mod_text[j] < byte_mem[w][k]? less: greater;
}

// 8.4???8.5:
// The prefix_lookup() procedure is supposed to find exactly one module name that has mod_text[1..l] as a prefix.
// Actually the algorithm silently accepts also the situation that some module name is a prefix of mod_text[1..l],
// because the user who painstakingly typed in more than necessary probably doesn't want to be told about the wasted effort.
//
// Recall that error messages are not printed during phase one.
// It is possible that the prefix_lookup() procedure will fail on the first pass, because there is no match,
// yet the second pass might detect no error if a matching module name has occurred after the offending prefix.
// In such a case the cross-reference information will be incorrect and ???WEAVE??? will report no error.
// However, such a mistake will be detected by the ???TANGLE??? processor.
name_pointer prefix_lookup(sixteen_bits l) {	// finds name extension
   name_pointer p ??? root;		// current node of the search tree
   name_pointer q ??? 0;			// another place to resume the search after one branch is done
   enum {0..max_names} count ??? 0;	// the number of hits
   name_pointer r ??? 0;			// begin search for the extension to be found at root of tree
   while (p ??? 0) {
      ModDiffT c ??? MatchNames(p, l);	// comparison between two names
      if (c ??? less) p ??? llink[p];
      else if (c ??? greater) p ??? rlink[p];
      else r ??? p, count???, q ??? rlink[p], p ??? llink[p];
      if (p ??? 0) p ??? q, q ??? 0;
   }
   if (count ??? 0) err_print("! Name does not match");
   else if (count ??? 1) err_print("! Ambiguous prefix");
   return r;	// the result will be 0 if there was no match
}
// 8.5???

// ??9. Lexical Scanning.
// ???9.1:
// Let us now consider the subroutines that read the ???WEB??? source file and break it into meaningful units.
// There are four such procedures: One simply skips to the next ??????@\ ?????? or ??????@*?????? that begins a module;
// another passes over the ???TeX??? text at the beginning of a module;
// the third passes over the ???TeX??? text in a ???Pas??? comment; and the last, which is the most interesting, gets the next token of a ???Pas??? text.

// 9.1???9.2: Globals in the outer block (16/34)
// But first we need to consider the low-level routine get_line() that takes care of merging change_file into web_file.
// The get_line() procedure also updates the line numbers for error messages.
int ii;				// general purpose for loop variable in the outer block
int line;			// the number of the current line in the current file
int other_line;			// the number of the current line in the input file that is not currently being read
enum {0..long_buf_size} limit;	// the last character position occupied in the buffer
enum {0..long_buf_size} loc;	// the next character position to be read from the buffer
bool input_has_ended;		// if true, there is no more input
bool changing;			// if true, the current line is from change_file
bool change_pending;		// if true, the current change is not yet recorded in changed_module[module_count]

// 9.2???9.3:
// As we change changing from true to false and back again,
// we must remember to swap the values of line and other_line so that the err_print() routine will be sure to report the correct line number.
inline void change_changing(void) {
   changing ??? !changing;
   int temp_line ??? other_line;	// used when interchanging line with other_line
   other_line ??? line, line ??? temp_line;	// line ??? other_line
}

// 9.3???9.4: Globals in the outer block (17/34)
// When changing is false, the next line of change_file is kept in change_buffer[0..change_limit],
// for purposes of comparison with the next line of web_file.
// After the change file has been completely input, we set change_limit ??? 0, so that no further matches will be made.
ASCII_code change_buffer[0..buf_size];
enum {0..buf_size} change_limit;	// the last position occupied in change_buffer

// 9.4???9.5:
// Here's a simple function that checks if the two buffers are different.
bool lines_dont_match(void) {
   if (change_limit ??? limit) return true;
   if (limit > 0) for (enum {0..buf_size} k ??? limit) if (change_buffer[k] ??? buffer[k]) return true;
   return false;
}

// 9.5???9.6:
// Procedure prime_the_change_buffer() sets change_buffer in preparation for the next matching operation.
// Since blank lines in the change file are not used for matching, we have change_limit ??? 0 && !changing if and only if the change file is exhausted.
// This procedure is called only when changing is true; hence error messages will be reported correctly.
void prime_the_change_buffer(void) {
   change_limit ??? 0;	// this value will be used if the change file ends
// ???9.7: Skip over comment lines in the change file; return if end of file
// While looking for a line that begins with ???@x??? in the change file, we allow lines that begin with ???@???, as long as they don't begin with ???@y??? or ???@z???
// (which would probably indicate that the change file is fouled up).
   while (true) {
      line???;
      if (!input_ln(change_file)) return;
      if (limit < 2) continue;
      if (buffer[0] ??? '@') continue;
      if (buffer[1] ??? 'X' && buffer[1] ??? 'Z') buffer[1] ??? buffer[1] + 'z' - 'Z';	// lowercasify
      if (buffer[1] ??? 'x') break;
      if (buffer[1] ??? 'y' || buffer[1] ??? 'z') {
         loc ??? 2; err_print("! Where is the matching @x?");

      }
   }
// 9.7???9.8: Skip to the next nonblank line; return if end of file
// Here we are looking at lines following the ???@x???.
   do {
      line???;
      if (!input_ln(change_file)) { err_print("! Change file ended after @x"); return; }
   } while (limit ??? 0);
   SwapBuffers();
}

// 9.6???9.9: Move buffer and limit to change_buffer and change_limit
inline void SwapBuffers(void) {
   change_limit ??? limit;
   if (limit > 0) for (enum {0..buf_size} k ??? limit) change_buffer[k] ??? buffer[k];
}

// 9.9???9.10:
// The following procedure is used to see if the next change entry should go into effect; it is called only when changing is false.
// The idea is to test whether or not the current contents of buffer matches the current contents of change_buffer.
// If not, there's nothing more to do; but if so, a change is called for:
// All of the text down to the ???@y??? is supposed to match.
// An error message is issued if any discrepancy is found.
// Then the procedure prepares to read the next line from change_file.
//
// When a match is found, the current module is marked as changed unless the first line after the ???@x???
// and after the ???@y??? both start with either '@*' or '@ ' (possibly preceded by whitespace).
inline void if_module_start_then_make_change_pending(bool A) {
   buffer[limit] ??? '!';
   for (loc ??? 0; buffer[loc] ??? ' ' || buffer[loc] ??? tab_mark; loc???);
   buffer[limit] ??? ' ';
   if (buffer[loc] ??? '@' && (buffer[loc + 1] ??? '*' || buffer[loc + 1] ??? ' ' || buffer[loc + 1] ??? tab_mark)) change_pending ??? A;
}

void check_change(void) {	// switches to change_file if the buffers match
   if (lines_dont_match()) return;
   change_pending ??? false;
   if (!changed_module[module_count]) {
      if_module_start_then_make_change_pending(true);
      if (!change_pending) changed_module[module_count] ??? true;
   }
   int n ??? 0;	// the number of discrepancies found
   while (true) {
      change_changing();	// now it's true
      line???;
      if (!input_ln(change_file)) {
         err_print("! Change file ended before @y");
         change_limit ??? 0, change_changing();	// false again
         return;
      }
   // ???9.11: If the current line starts with ???@y???, report any discrepancies and return
      if (limit > 1 && buffer[0] ??? '@') {
         if (buffer[1] ??? 'X' && buffer[1] ??? 'Z') buffer[1] ??? buffer[1] + 'z' - 'Z';	// lowercasify
         if (buffer[1] ??? 'x' || buffer[1] ??? 'z') loc ??? 2, err_print("! Where is the matching @y?");
         else if (buffer[1] ??? 'y') {
            if (n > 0) loc ??? 2, err_print("! Hmm... %1d of the preceding lines failed to match", n);
            return;
         }
      }
      SwapBuffers();
      change_changing();	// now it's false
      line???;
      if (!input_ln(web_file)) { err_print("! WEB file ended during a change"), input_has_ended ??? true; return; }
      if (lines_dont_match()) n???;
   }
}

// 9.10???9.12:
// The reset_input() procedure, which gets ???WEAVE??? ready to read the user's ???WEB??? input, is used at the beginning of phases one and two.
void reset_input(void) {
   open_input(), line ??? 0, other_line ??? 0;
   changing ??? true, prime_the_change_buffer(), change_changing();
   limit ??? 0, loc ??? 1, buffer[0] ??? ' ', input_has_ended ??? false;
}

// 9.12???9.13:
// The get_line() procedure is called when loc > limit;
// it puts the next line of merged input into the buffer and updates the other variables appropriately. A space is placed at the right end of the line.
void get_line(void) {	// inputs the next line
   while (true) {
      if (changing) {
      // ???9.15: Read from change_file and maybe turn off changing
         line???;
         if (!input_ln(change_file)) err_print("! Change file ended without @z"), buffer[0] ??? '@', buffer[1] ??? 'z', limit ??? 2;
         if (limit > 0) {	// check if the change has ended
            if (change_pending) {
               if_module_start_then_make_change_pending(false);
               if (change_pending) changed_module[module_count] ??? true, change_pending ??? false;
            }
            buffer[limit] ??? ' ';
            if (buffer[0] ??? '@') {
               if (buffer[1] ??? 'X' && buffer[1] ??? 'Z') buffer[1] ??? buffer[1] + 'z' - 'Z';	// lowercasify
               if (buffer[1] ??? 'x' || buffer[1] ??? 'y') loc ??? 2, err_print("! Where is the matching @z?");
               else if (buffer[1] ??? 'z') prime_the_change_buffer(), change_changing();
            }
         }
      // 9.15???
         if (changing) break;
      }
   // ???9.14: Read from web_file and maybe turn on changing
      line???;
      if (!input_ln(web_file)) input_has_ended ??? true;
      else if (limit ??? change_limit && buffer[0] ??? change_buffer[0] && change_limit > 0) check_change();
   // 9.14???
      if (!changing) break;
   }
   loc ??? 0, buffer[limit] ??? ' ';
}

// 9.13???9.17:
// Control codes in ???WEB???, which begin with ??????@??????, are converted into a numeric code designed to simplify ???WEAVE???'s logic;
// for example, larger numbers are given to the control codes that denote more significant milestones,
// and the code of new_module should be the largest of all.
// Some of these numeric control codes take the place of ASCII control codes that will not otherwise appear in the output of the scanning routines.
#define ignore		0x00	// control code of no interest to ???WEAVE???
#define verbatim	0x02	// extended ASCII alpha will not appear
#define force_line	0x03	// extended ASCII beta will not appear
#define begin_comment	0x09	// ASCII tab mark will not appear
#define end_comment	0x0a	// ASCII line feed will not appear
#define octal		0x0c	// ASCII form feed will not appear
#define hex		0x0d	// ASCII carriage return will not appear
#define double_dot	0x20	// ASCII space will not appear except in strings
#define no_underline	0x7d	// this code will be intercepted without confusion
#define underline	0x7e	// this code will be intercepted without confusion
#define param		0x7f	// ASCII delete will not appear
#define xref_roman	0x83	// control code for ??????@^??????
#define xref_wildcard	0x84	// control code for ??????@:??????
#define xref_typewriter	0x85	// control code for ??????@.??????
#define TeX_string	0x86	// control code for ??????@t??????
#define check_sum	0x87	// control code for ??????@$??????
#define join		0x88	// control code for ??????@&??????
#define thin_space	0x89	// control code for ??????@,??????
#define math_break	0x8a	// control code for ??????@|??????
#define line_break	0x8b	// control code for ??????@/??????
#define big_line_break	0x8c	// control code for ??????@#??????
#define no_line_break	0x8d	// control code for ??????@+??????
#define pseudo_semi	0x8e	// control code for ??????@;??????
#define format		0x8f	// control code for ??????@f??????
#define definition	0x90	// control code for ??????@d??????
#define begin_Pascal	0x91	// control code for ??????@p??????
#define module_name	0x92	// control code for ??????@<??????
#define new_module	0x93	// control code for ??????@ ?????? and ??????@*??????

// 9.17???9.18:
// Control codes are converted from ASCII to ???WEAVE???'s internal representation by the control_code() routine.
eight_bits control_code(ASCII_code c) {	// convert c after ???@???
   switch (c) {
      case '@': return '@';	// ???quoted??? at sign
      case '\'': return octal;	// precedes octal constant
      case '"': return hex;	// precedes hexadecimal constant
      case '$': return check_sum;	// precedes check sum constant
      case ' ': case tab_mark: case '*': return new_module;	// beginning of a new module
      case '=': return verbatim;
      case '\\': return force_line;
      case 'D': case 'd': return definition;	// macro definition
      case 'F': case 'f': return format;	// format definition
      case '{': return begin_comment;	// begin-comment delimiter
      case '}': return end_comment;	// end-comment delimiter
      case 'P': case 'p': return begin_Pascal;	// ???Pas??? text in unnamed module
      case '&': return join;	// concatenate two tokens
      case '<': return module_name;	// beginning of a module name
      case '>': err_print("! Extra @>"); return ignore;	// end of module name should not be discovered in this way
      case 'T': case 't': return TeX_string;	// ???TeX??? box within ???Pas???
      case '!': return underline;	// set definition flag
      case '?': return no_underline;	// reset definition flag
      case '^': return xref_roman;	// index entry to be typeset normally
      case ':': return xref_wildcard;	// index entry to be in user format
      case '.': return xref_typewriter;	// index entry to be in typewriter type
      case ',': return thin_space;	// puts extra space in ???Pas??? format
      case '|': return math_break;	// allows a break in a formula
      case '/': return line_break;	// forces end-of-line in ???Pas??? format
      case '#': return big_line_break;	// forces end-of-line and some space besides
      case '+': return no_line_break;	// cancels end-of-line down to single space
      case ';': return pseudo_semi;	// acts like a semicolon, but is invisible
   // ???9.19: Special control codes allowed only when debugging
   // If ???WEAVE??? is compiled with debugging commands, one can write ???@2???, ???@1???, and ???@0??? to turn tracing fully on, partly on, and off, respectively.
#if DEBUG
      case '0': case '1': case '2': tracing ??? c - '0'; return ignore;
#endif // DEBUG
   // 9.19???
      default: err_print("! Unknown control code"); return ignore;
   }
}

// 9.18???9.20:
// The skip_limbo() routine is used on the first pass to skip through portions of the input that are not in any modules, i.e., that precede the first module.
// After this procedure has been called, the value of input_has_ended will tell whether or not a new module has actually been found.
void skip_limbo(void) {	// skip to next module
   while (true)
      if (loc > limit) {
         get_line();
         if (input_has_ended) return;
      } else {
         buffer[limit + 1] ??? '@';
         while (buffer[loc] ??? '@') loc???;
         if (loc ??? limit) {
            loc ??? loc + 2;
            ASCII_code c ??? buffer[loc - 1];	// character following ???@???
            if (c ??? ' ' || c ??? tab_mark || c ??? '*') return;
         }
      }
}

// 9.20???9.21:
// The skip_TeX() routine is used on the first pass to skip through the ???TeX??? code at the beginning of a module.
// It returns the next control code or ??????|?????? found in the input.
// A new_module is assumed to exist at the very end of the file.
eight_bits skip_TeX(void) {	// skip past pure ???TeX??? code
   while (true) {
      if (loc > limit) {
         get_line();
         if (input_has_ended) break;
      }
      buffer[limit + 1] ??? '@';
      do {
         eight_bits c ??? buffer[loc???];	// control code found
         if (c ??? '|') return c;
      } while (c ??? '@');
      if (loc ??? limit) return control_code(buffer[loc???]);
   }
   return new_module;
}

// 9.21???9.22
// The skip_comment() routine is used on the first pass to skip through ???TeX??? code in ???Pas??? comments.
// The bal parameter tells how many left braces are assumed to have been scanned when this routine is called,
// and the procedure returns a corresponding value of bal at the point that scanning has stopped.
// Scanning stops either at a ??????|?????? that introduces ???Pas??? text,
// in which switch (the returned value is positive, or it stops at the end) { the comment, in which case the returned value is zero.
// The scanning also stops in anomalous situations when the comment doesn't end or when it contains an illegal use of ???@???.
// One should call skip_comment(1) when beginning to scan a comment.
eight_bits skip_comment(eight_bits bal) {	// skips ???TeX??? code in comments
   while (true) {
      if (loc > limit) {
         get_line();
         if (input_has_ended) { bal ??? 0; break; }	// an error message will occur in phase two
      }
      ASCII_code c ??? buffer[loc???];	// the current character
      if (c ??? '|') break;
   // ???9.23: Do special things when c ??? '@', '\\', '{', '}'; break at end
      else if (c ??? '@') {
         c ??? buffer[loc];
         if (c ??? ' ' && c ??? tab_mark && c ??? '*') loc???;
         else { loc???; bal ??? 0; break; }	// an error message will occur in phase two
      } else if (c ??? '\\' && buffer[loc] ??? '@') loc???;
      else if (c ??? '{') bal???;
      else if (c ??? '}' && ???bal ??? 0) break;
   // 9.23???
   }
   return bal;
}
// 9.22???

// ??10. Inputting the Next Token.
// ???10.1: Globals in the outer block (18/34)
// As stated above, ???WEAVE???'s most interesting lexical scanning routine is the get_next() function that inputs the next token of ???Pas??? input.
// However, get_next() is not especially complicated.

// The result of get_next() is either an ASCII code for some special character, or it is a special code representing a pair of characters
// (e.g., ?????? ??? ?????? or ??????..??????), or it is the numeric value computed by the control_code() procedure, or it is one of the following special codes:
// ??? exponent:	The ??????E?????? in a real constant.
// ??? identifier:	In this case the global variables id_first and id_loc will have been set to the appropriate values needed by the id_lookup() routine.
// ??? string:	In this case the global variables id_first and id_loc will have been set to the beginning and ending-plus-one locations in the buffer.
//		The string ends with the first reappearance of its initial delimiter;
//		thus, for example, ???'This isn''t a single string'??? will be treated as two consecutive strings, the first being ???'This isn'???.
//		Furthermore, some of the control codes cause get_next() to take additional actions:
// ??? xref_roman, xref_wildcard, xref_typewriter, TeX_string:
//		The values of id_first and id_loc will be set so that the string in question appears in buffer[id_first..(id_loc - 1)].
// ??? module_name:	In this case the global variable cur_module will point to the byte_start[] entry for the module name that has just been scanned.
// If get_next() sees ??????@!?????? or ??????@???????, it sets xref_switch to def_flag or zero and goes on to the next token.

// A global variable called scanning_hex is set true during the time that the letters ???A??? through ???F??? should be treated as if they were digits.
#define exponent	0x80	// ???E??? or ???e??? following a digit
#define string		0x81	// ???Pas??? string or ???WEB??? precomputed string
#define identifier	0x82	// ???Pas??? identifier or reserved word

name_pointer cur_module;	// name of module just scanned
// ???10.2: Set initial values (12/20)
bool scanning_hex ??? false;	// are we scanning a hexadecimal constant?
// 10.2???
// 10.1???10.3
#if DEBUG
#   define Return(X) return NeedDebug? (DebugHelp(), (X)): (X)
#else
#   define Return(X) return (X)
#endif // DEBUG

eight_bits get_next(void) {	// produces the next input token
   while (true) {
      if (loc > limit) {
         get_line(); if (input_has_ended) break;
      }
      eight_bits c ??? buffer[loc???];		// the current character
      if (scanning_hex) {
      // ???10.4: Go to found if c is a hexadecimal digit, otherwise set scanning_hex ??? false
         if (c ??? '0' && c ??? '9' || c ??? 'A' && c ??? 'F') Return(c);
         else scanning_hex ??? false
      // 10.4???
      }
      switch (c) {
      // ???10.3:
      // As one might expect, get_next() consists mostly of a big switch that branches to the various special cases that can arise.
         case 'A': case 'B': case 'C': case 'D': case 'E': case 'F': case 'G': case 'H': case 'I': case 'J': case 'K': case 'L': case 'M':
         case 'N': case 'O': case 'P': case 'Q': case 'R': case 'S': case 'T': case 'U': case 'V': case 'W': case 'X': case 'Y': case 'Z':
         case 'a': case 'b': case 'c': case 'd': case 'e': case 'f': case 'g': case 'h': case 'i': case 'j': case 'k': case 'l': case 'm':
         case 'n': case 'o': case 'p': case 'q': case 'r': case 's': case 't': case 'u': case 'v': case 'w': case 'x': case 'y': case 'z':
      // 10.3???10.6: Get an identifier
            if ((c ??? 'E' || c ??? 'e') && loc > 1 && buffer[loc - 2] ??? '9' && buffer[loc - 2] ??? '0') Return(exponent);
            id_first ??? ???loc;
            eight_bits d;
            do d ??? buffer[???loc]; while (d ??? '0' && (d ??? '9' || d ??? 'A') && (d ??? 'Z' || d ??? 'a') && d ??? 'z' || d ??? '_');
            id_loc ??? loc;
         Return(identifier);
      // 10.6???
         case '\'': case '"': {
      // ???10.7: Get a string
      // A string that starts and ends with single or double quote marks is scanned by the following piece of the program.
            id_first ??? loc - 1;
            eight_bits d;
            do {
               d ??? buffer[loc???];
               if (loc > limit) { err_print("! String constant didn't end"), loc ??? limit; break; }
            } while (d ??? c);
            id_loc ??? loc;
         }
         Return(string);
      // 10.7???
         case '@':
         // ???10.8: Get control code and possible module name
         // After an ???@??? sign has been scanned, the next character tells us whether there is more work to do.
            c ??? control_code(buffer[loc???]);
            if (c ??? underline) {
               xref_switch ??? def_flag; continue;
            } else if (c ??? no_underline) {
               xref_switch ??? 0; continue;
            } else if (c ??? TeX_string && c ??? xref_roman) {
            // ???10.14: Scan to the next ???@>???
               id_first ??? loc, buffer[limit + 1] ??? '@';
               for (; buffer[loc] ??? '@'; loc???);
               id_loc ??? loc;
               if (loc > limit) err_print("! Control text didn't end"), loc ??? limit;
               else {
                  loc += 2;
                  if (buffer[loc - 1] ??? '>') err_print("! Control codes are forbidden in control text");
               }
            // 10.14???
            } else if (c ??? hex) scanning_hex ??? true;
            else if (c ??? module_name) {
            // ???10.9: Scan the module name and make cur_module point to it
            // The occurrence of a module name sets xref_switch to zero, because the module name might (for example) follow ????var????.
            // ???10.11: Put module name into mod_text[1..k]
               enum {0..longest_name} k ??? 0;	// index into mod_text
               while (true) {
                  if (loc > limit) {
                     get_line();
                     if (input_has_ended) { err_print("! Input ended in section name"), loc ??? 1; break; }
                  }
                  eight_bits d ??? buffer[loc];
               // ???10.12: If end of name, break
                  if (d ??? '@') {
                     d ??? buffer[loc + 1];
                     if (d ??? '>') { loc += 2; break; }
                     else if (d ??? ' ' || d ??? tab_mark || d ??? '*') { err_print("! Section name didn't end"); break; }
                     mod_text[???k] ??? '@', loc???;	// now d ??? buffer[loc] again
                  }
               // 10.12???
                  loc???; if (k < longest_name - 1) k???;
                  if (d ??? ' ' || d ??? tab_mark) {
                     d ??? ' '; if (mod_text[k - 1] ??? ' ') k???;
                  }
                  mod_text[k] ??? d;
               }
            // ???10.13: Check for overlong name
               if (k ??? longest_name - 2) {
                  print("\n! Section name too long: ");
                  for (enum {0..longest_name} j ??? 1 ??? 25) print("%c", xchr[mod_text[j]]);
                  print("..."), mark_harmless();
               }
            // 10.13???
               if (mod_text[k] ??? ' ' && k > 0) k???
            // 10.11???
               cur_module ???
                  k ??? 3? mod_lookup(k):
                  mod_text[k] ??? '.' && mod_text[k - 1] ??? '.' && mod_text[k - 2] ??? '.'? prefix_lookup(k - 3): mod_lookup(k),
               xref_switch ??? 0;
            // 10.9???
            } else if (c ??? verbatim) {
            // ???10.15: Scan a verbatim string
            // A verbatim ???Pas??? string will be treated like ordinary strings, but with no surrounding delimiters.
            // At the present point in the program we have buffer[loc - 1] ??? verbatim;
            // we must set id_first to the beginning of the string itself, and id_loc to its ending-plus-one location in the buffer.
            // We also set loc to the position just after the ending delimiter.
               id_first ??? loc???;
               buffer[limit + 1] ??? '@', buffer[limit + 2] ??? '>';
               for (; buffer[loc] ??? '@' || buffer[loc + 1] ??? '>'; loc???);
               if (loc ??? limit) err_print("! Verbatim string didn't end");
               id_loc ??? loc, loc += 2;
            // 10.15???
            }
         // 10.8???
         Return(c);
      // ???10.5: Compress two-symbol combinations like ?????? ??? ??????
      // Note that the following code substitutes ???@{??? and ???@\???} for the respective combinations ??????(*?????? and ??????*)??????.
      // Explicit braces should be used for ???TeX??? comments in ???Pas??? text.
   #define compress(A) if (loc ??? limit) { loc???; Return(A); }
         case '.':
            if (buffer[loc] ??? '.') compress(double_dot);
            else if (buffer[loc] ??? ')') compress(']');
         Return(c);
         case ':':
            if (buffer[loc] ??? '=') compress(left_arrow);
         Return(c);
         case '=':
            if (buffer[loc] ??? '=') compress(equivalence_sign);
         Return(c);
         case '>':
            if (buffer[loc] ??? '=') compress(greater_or_equal);
         Return(c);
         case '<':
            if (buffer[loc] ??? '=') compress(less_or_equal);
            else if (buffer[loc] ??? '>') compress(not_equal);
         Return(c);
         case '(':
            if (buffer[loc] ??? '*') compress(begin_comment);
            else if (buffer[loc] ??? '.') compress('[');
         Return(c);
         case '*':
            if (buffer[loc] ??? ')') compress(end_comment);
         Return(c);
      // 10.5???
         case ' ': case tab_mark: continue;	// ignore spaces and tabs
         case '}':
            err_print("! Extra }");
         continue;
         default:
            if (c < 0x80) Return(c);
         continue;	// ignore nonstandard characters
      }
   }
   Return(new_module);
}
// 10.3???

// ??11. Phase one Processing.
// ???11.1: Globals in the outer block (19/34)
// We now have accumulated enough subroutines to make it possible to carry out ???WEAVE???'s first pass over the source file.
// If everything works right, both phase one and phase two of ???WEAVE??? will assign the same numbers to modules,
// and these numbers will agree with what ???TANGLE??? does.

// The global variable next_control often contains the most recent output of get_next();
// in interesting cases, this will be the control code that ended a module or part of a module.
eight_bits next_control;	// control code waiting to be acting upon

// 11.1???11.4:
// The Pascal_xref() subroutine stores references to identifiers in ???Pas??? text material beginning with the current value of next_control
// and continuing until next_control is ??????{?????? or ??????|??????, or until the next ???milestone??? is passed (i.e., next_control ??? format).
// If next_control ??? format when Pascal_xref() is called, nothing will happen;
// but if next_control ??? '|' upon entry, the procedure assumes that this is the ??????|?????? preceding ???Pas??? text that is to be processed.

// The program uses the fact that our internal code numbers satisfy the relations xref_roman ??? identifier + roman
// and xref_wildcard ??? identifier + wildcard and xref_typewriter ??? identifier + typewriter and normal ??? 0.
// An implied ??????@!?????? is inserted after ????function????, ????procedure????, ????program????, and ????var????.
void Pascal_xref(void) {	// makes cross references for ???Pas??? identifiers
   while (next_control < format) {
      if (next_control ??? identifier && next_control ??? xref_typewriter) {
         name_pointer p ??? id_lookup(next_control - identifier);	// a referenced name
         new_xref(p);
         if (ilk[p] ??? proc_like || ilk[p] ??? var_like) xref_switch ??? def_flag;	// implied ??????@!??????
      }
      next_control ??? get_next();
      if (next_control ??? '|' || next_control ??? '{') return;
   }
}

// 11.4???11.5:
// The outer_xref() subroutine is like Pascal_xref() but it begins with next_control ??? '|' and ends with next_control ??? format.
// Thus, it handles ???Pas??? text with embedded comments.
void outer_xref(void) {	// extension of Pascal_xref()
   while (next_control < format)
      if (next_control ??? '{') Pascal_xref();
      else {
         eight_bits bal ??? skip_comment(1);	// brace level in comment
         next_control ??? '|';
         while (bal > 0) Pascal_xref(), bal ??? next_control ??? '|'? skip_comment(bal): 0;	// for 0, an error will be reported in phase two
      }
}

// 11.5???11.7: Globals in the outer block (20/34)
// During the definition and ???Pas??? parts of a module, cross references are made for all identifiers except reserved words;
// however, the identifiers in a format definition are referenced even if they are reserved.
// The ???TeX??? code in comments is, of course, ignored, except for ???Pas??? portions enclosed in ???pb???;
// the text of a module name is skipped entirely, even if it contains ???pb??? constructions.

// The variables lhs and rhs point to the respective identifiers involved in a format definition.
name_pointer lhs, rhs;	// indices into byte_start[] for format identifiers

// 11.7???11.11: Globals in the outer block (21/34)
// After phase one has looked at everything, we want to check that each module name was both defined and used.
// The variable cur_xref will point to cross references for the current module name of interest.
xref_number cur_xref;	// temporary cross reference pointer

// 11.11???11.12:
// The following recursive procedure walks through the tree of module names and prints out anomalies.
void mod_check(name_pointer p) {	// print anomalies in subtree p
   if (p > 0) {
      mod_check(llink[p]);
      cur_xref ??? xref[p];
      if (num(cur_xref) < def_flag) print("\n! Never defined: <"), print_id(p), print(">"), mark_harmless();
      for (; num(cur_xref) ??? def_flag; cur_xref ??? xlink(cur_xref));
      if (cur_xref ??? 0) print("\n! Never used: <"), print_id(p), print(">"), mark_harmless();
      mod_check(rlink[p]);
   }
}
// 11.12???

// ??12. Low-Level Output Routines.
// ???12.1: Globals in the outer block (22/34)
// The ???TeX??? output is supposed to appear in lines at most line_length characters long, so we place it into an output buffer.
// During the output process, out_line will hold the current line number of the line about to be output.

// ???12.6: Set initial values (15/20)
// The break_out() routine is called just before the output buffer is about to overflow.
// To make this routine a little faster, we initialize position 0 of the output buffer to ??????\??????; this character isn't really output.
ASCII_code out_buf[0..line_length] ??? '\\';	// assembled characters
// 12.6???12.4: Set initial values (14/20)
enum {0..line_length} out_ptr ??? 1;	// number of characters in out_buf
int out_line ??? 1;	// coordinates of next line to be output
// 12.4???

// 12.1???12.2:
// The flush_buffer() routine empties the buffer up to a given breakpoint, and moves any remaining characters to the beginning of the next line.
// If the per_cent parameter is true, a '%' is appended to the line that is being output;
// in this case the breakpoint b should be strictly less than line_length.
// If the per_cent parameter is false, trailing blanks are suppressed.
// The characters emptied from the buffer form a new line of output;
// if the carryover parameter is true, a '%' in that line will be carried over to the next line
// (so that ???TeX??? will ignore the completion of commented-out text).
void flush_buffer(eight_bits b, bool per_cent, bool carryover) {	// outputs out_buf[1..b], where b ??? out_ptr
   enum {0..line_length} j ??? b;
   if (!per_cent) for (; j ??? 0 && out_buf[j] ??? ' '; j???); // remove trailing blanks
   for (enum {0..line_length} k ??? 1 ??? j) write(tex_file, "%c", xchr[out_buf[k]]);
   if (per_cent) write(tex_file, "%c", xchr['%']);
   write(tex_file, "\n"), out_line???;
   if (carryover) for (enum {0..line_length} k ??? 1 ??? j) if (out_buf[k] ??? '%') if (k ??? 1 || out_buf[k - 1] ??? '\\') {	// comment mode should be preserved
      out_buf[b???] ??? '%'; break;
   }
   if (b < out_ptr) for (enum {0..line_length} k ??? b + 1 ??? out_ptr) out_buf[k - b] ??? out_buf[k];
   out_ptr -= b;
}

// 12.2???12.3:
// When we are copying ???TeX??? source material, we retain line breaks that occur in the input,
// except that an empty line is not output when the ???TeX??? source line was nonempty.
// For example, a line of the ???TeX??? file that contains only an index cross-reference entry will not be copied.
// The finish_line() routine is called just before get_line() inputs a new line,
// and just after a line break token has been emitted during the output of translated ???Pas??? text.
void finish_line(void) {	// do this at the end of a line
   if (out_ptr > 0) flush_buffer(out_ptr, false, false);
   else {
      for (enum {0..buf_size} k ??? 0 ??? limit) if (buffer[k] ??? ' ' && buffer[k] ??? tab_mark) return;
      flush_buffer(0, false, false);
   }
}

// 12.3???12.5:
// When we wish to append the character c to the output buffer, we write ???out1(c)???; this will cause the buffer to be emptied if it was already full.
// Similarly, ???outS(A, ...)??? appends characters in the style of ???printf(A, ...)???.
// A line break will occur at a space or after a single-nonletter ???TeX??? control sequence.

// Editor's Note:
// ???	out(), out2(), out3(), out4(), out5(), from the orignal, have been combined into out1() and outS().
inline void out1(ASCII_code Ch) {
   if (out_ptr ??? line_length) break_out(); else out_buf[???out_ptr] ??? Ch;
}

inline void outS(ASCII_code *A, ...) {
   va_list AP; va_start(AP, A);
   for (; *A ??? '\0'; A???) {
      ASCII_code Ch = *A;
      if (Ch ??? '%') {
         Ch = *???A;
         if (Ch ??? '\0') A???, Ch = '%'; else if (Ch ??? 'c') Ch = va_arg(AP, ASCII_code);
      }
      if (out_ptr ??? line_length) break_out(); else out_buf[???out_ptr] ??? Ch;
   }
   va_end(AP);
}

// 12.5???12.7:
// A long line is broken at a blank space or just before a backslash that isn't preceded by another backslash.
// In the latter case, a '%' is output at the break.
void break_out(void) {	// finds a way to break the output line
   for (enum {0..line_length} k ??? out_ptr; k > 0; k???) {
      ASCII_code d ??? out_buf[k];	// character from the buffer
      if (d ??? ' ') { flush_buffer(k, false, true); return; }
      else if (d ??? '\\' && out_buf[k - 1] ??? '\\') { flush_buffer(k - 1, true, true); return; } // in this case k > 1
   }
// ???12.8: Print warning message, break the line
// We get to this module only in unusual cases that the entire output line
   // consists of a string of backslashes followed by a string of nonblank non-backslashes.
// In such cases it is almost always safe to break the line by putting a '%' just before the last character.
   print("\n! Line had to be broken (output l.%1d):\n", out_line);
   for (enum {0..line_length} k ??? 1 ??? out_ptr - 1) print(xchr[out_buf[k]]);
   print("\n"), mark_harmless();
   flush_buffer(out_ptr - 1, true, true);
// 12.8???
}

// 12.7???12.9: Globals in the outer block (23/34)
// Here is a procedure that outputs a module number in decimal notation.
enum {10} dig[5];	// digits to output

// 12.9???12.10:
// The number to be converted by out_mod() is known to be less than def_flag, so it cannot have more than five decimal digits.
// If the module is changed, we output ??????\*?????? just after the number.
void out_mod(int m) {	// output a module number
   int a ??? m;	// accumulator
   enum {6} k ??? 0;	// index into dig
   do dig[k???] ??? a%10, a /= 10; while (a ??? 0);
   do out1(dig[???k] + '0'); while (k ??? 0);
   if (changed_module[m]) outS("\\*");

}

// 12.10???12.11:
// The out_name() subroutine is used to output an identifier or index entry, enclosing it in braces.
void out_name(name_pointer p) {	// outputs a name
   out1('{');
   enum {ww} w ??? p%ww;		// row of byte_mem[]
   for (enum {0..max_bytes} k ??? byte_start[p] ??? byte_start[p + ww] - 1) {
      if (byte_mem[w][k] ??? '_') out1('\\');
      out1(byte_mem[w][k]);
   }
   out1('}');
}
// 12.11???

// ??13. Routines that Copy ???TeX??? Material.
// ???13.1:
// During phase two, we use the subroutines copy_limbo(), copy_TeX(), and copy_comment()
// in place of the analogous skip_limbo(), skip_TeX(), and skip_comment() that were used in phase one.

// The copy_limbo() routine, for example, takes ???TeX??? material that is not part of any module and transcribes it almost verbatim to the output file.
// No ??????@?????? signs should occur in such material except in ??????@@?????? pairs; such pairs are replaced by singletons.
void copy_limbo(void) {	// copy ???TeX??? code until the next module begins
   while (true)
      if (loc > limit) {
         finish_line(), get_line(); if (input_has_ended) break;
      } else {
         buffer[limit + 1] ??? '@';
      // ???13.2: Copy up to control code, break if finished
         for (; buffer[loc] ??? '@'; loc???) out1(buffer[loc]);
         if (loc ??? limit) {
            loc += 2;
            ASCII_code c ??? buffer[loc - 1];	// character following ???@??? sign
            if (c ??? ' ' || c ??? tab_mark || c ??? '*') break;
            else if (c ??? 'z' && c ??? 'Z') {
               out1('@');
               if (c ??? '@') err_print("! Double @ required outside of sections");
            }
         }
      // 13.2???
      }
}

// 13.1???13.3:
// The copy_TeX() routine processes the ???TeX??? code at the beginning of a module; for example, the words you are now reading were copied in this way.
// It returns the next control code or ??????|?????? found in the input.
eight_bits copy_TeX(void) {	// copy pure ???TeX??? material
   while (true) {
      if (loc > limit) {
         finish_line(), get_line(); if (input_has_ended) break;
      }
      buffer[limit + 1] ??? '@';
   // ???13.4: Copy up to ??????|?????? or control code, return if finished
   // We don't copy spaces or tab marks into the beginning of a line.
   // This makes the test for empty lines in finish_line() work.
      eight_bits c;	// control code found
      do {
         c ??? buffer[loc???];
         if (c ??? '|') return c;
         else if (c ??? '@') {
            out1(c);
            if (out_ptr ??? 1 && (c ??? ' ' || c ??? tab_mark)) out_ptr???;
         }
      } while (c ??? '@');
      if (loc ??? limit) return control_code(buffer[loc???]);
   // 13.4???
   }
   return new_module;
}

// 13.3???13.5:
// The copy_comment() uses and returns a brace-balance value, following the conventions of skip_comment() above.
// Instead of copying the ???TeX??? material into the output buffer, this procedure copies it into the token memory.
// The abbreviation app_tok(t) is used to append token t to the current token list,
// and it also makes sure that it is possible to append at least one further token without overflow.
inline void app_tok(sixteen_bits A) {
   if (tok_ptr + 2 > max_toks) overflow("token");
   tok_mem[tok_ptr???] ??? A;
}

eight_bits copy_comment(eight_bits bal) {	// copies ???TeX??? code in comments
   while (true) {
      if (loc > limit) {
         get_line();
         if (input_has_ended) {
            err_print("! Input ended in mid-comment"), loc ??? 1, ClearBal();
            break;
         }
      }
      ASCII_code c ??? buffer[loc???];	// current character being copied
      if (c ??? '|') break;
      app_tok(c);
   // ???13.6: Copy special things when c ??? '@', '\\', '{', '}'; break at end
      if (c ??? '@' && buffer[loc???] ??? '@') {
         err_print("! Illegal use of @ in comment"), loc -= 2, tok_ptr???, ClearBal();
         break;
      } else if (c ??? '\\' && buffer[loc] ??? '@') app_tok(buffer[loc???]);
      else if (c ??? '{') bal???;
      else if (c ??? '}' && ???bal ??? 0) break;
   // 13.6???
   }
   return bal;
}

// 13.5???13.7: Clear bal
// When the comment has terminated abruptly due to an error, we output enough right braces to keep ???TeX??? happy.
inline void ClearBal(void) {
   app_tok(' ');	// this is done in case the previous character was ??????\??????
   do app_tok('}'); while (???bal > 0);
}
// 13.7???

// ??14. Parsing.
// ???14.1:
// The most intricate part of ???WEAVE??? is its mechanism for converting ???Pas??? -like code into ???TeX??? code,
// and we might as well plunge into this aspect of the program now.
// A ???bottom up??? approach is used to parse the ???Pas??? -like material,
// since ???WEAVE??? must deal with fragmentary constructions whose overall ???part of speech??? is not known.

// At the lowest level, the input is represented as a sequence of entities that we shall call {\it scraps},
// where each scrap of information consists of two parts, its {\it category} and its {\it translation}.
// The category is essentially a syntactic class, and the translation is a token list that represents ???TeX??? code.
// Rules of syntax and semantics tell us how to combine adjacent scraps into larger ones,
// and if we are lucky an entire ???Pas??? text that starts out as hundreds of small scraps will join together into one gigantic scrap
// whose translation is the desired ???TeX??? code.
// If we are unlucky, we will be left with several scraps that don't combine; their translations will simply be output, one by one.

// The combination rules are given as context-sensitive productions that are applied from left to right.
// Suppose that we are currently working on the sequence of scraps s??? s??? ??? s_n.
// We try first to find the longest production that applies to an initial substring s??? s??? ???;
// but if no such productions exist, we find to find the longest production applicable to the next substring s??? s??? ???;
// and if that fails, we try to match s??? s??? ???, etc.

// A production applies if the category codes have a given pattern.
// For example, one of the productions is
//	open math semi ??? open math
// and it means that three consecutive scraps whose respective categories are open, math, and semi
// are converted to two scraps whose categories are open and math.
// This production also has an associated rule that tells how to combine the translation parts:
//	O???	= O???
//	M???	= M??? S ???\,??? ???opt??? ???5???
// This means that the open scrap has not changed,
// while the new math scrap has a translation M??? composed of the translation M??? of the original math scrap
// followed by the translation S of the semi scrap followed by ??????\,?????? followed by ??????opt?????? followed by ??????5??????.
// (In the ???TeX??? file, this will specify an additional thin space after the semicolon, followed by an optional line break with penalty 50.)
// Translation rules use subscripts to distinguish between translations of scraps whose categories have the same initial letter;
// these subscripts are assigned from left to right.

// ???WEAVE??? also has the production rule
//	semi ??? terminator
// (meaning that a semicolon can terminate a ???Pas??? statement).
// Since productions are applied from left to right, this rule will be activated only if the semi is not preceded by scraps that match other productions;
// in particular, a semi that is preceded by ???open math??? will have disappeared because of the production above,
// and such semicolons do not act as statement terminators.
// This incidentally is how ???WEAVE??? is able to treat semicolons in two distinctly different ways,
// the first of which is intended for semicolons in the parameter list of a procedure declaration.

// The translation rule corresponding to semi ??? terminator is
//	T = S
// but we shall not mention translation rules in the common case that the translation of the new scrap on the right-hand side
// is simply the concatenation of the disappearing scraps on the left-hand side.

// 14.1???14.2:
// Here is a list of the category codes that scraps can have.
#define simp		1	// the translation can be used both in horizontal mode and in math mode of ???TeX???
#define math		2	// the translation should be used only in ???TeX??? math mode
#define intro		3	// a statement is expected to follow this, after a space and an optional break
#define open		4	// denotes an incomplete parenthesized quantity to be used in math mode
#define beginning	5	// denotes an incomplete compound statement to be used in horizontal mode
#define close		6	// ends a parenthesis or compound statement
#define alpha		7	// denotes the beginning of a clause
#define omega		8	// denotes the ending of a clause and possible comment following
#define semi		9	// denotes a semicolon and possible comment following it
#define terminator	10	// something that ends a statement or declaration
#define stmt		11	// denotes a statement or declaration including its terminator
#define cond		12	// precedes an ????if???? clause that might have a matching ?? else????
#define clause		13	// precedes a statement after which indentation ends
#define colon		14	// denotes a colon
#define exp		15	// stands for the E in a floating point constant
#define proc		16	// denotes a procedure or program or function heading
#define case_head	17	// denotes a case statement or record heading
#define record_head	18	// denotes a record heading without indentation
#define var_head	19	// denotes a variable declaration heading
#define elsie		20	// ?? else????
#define casey		21	// ????case????
#define mod_scrap	22	// denotes a module name

#if DEBUG
void print_cat(eight_bits c) {	// symbolic printout of a category
   switch (c) {
      case simp: print("simp"); break;
      case math: print("math"); break;
      case intro: print("intro"); break;
      case open: print("open"); break;
      case beginning: print("beginning"); break;
      case close: print("close"); break;
      case alpha: print("alpha"); break;
      case omega: print("omega"); break;
      case semi: print("semi"); break;
      case terminator: print("terminator"); break;
      case stmt: print("stmt"); break;
      case cond: print("cond"); break;
      case clause: print("clause"); break;
      case colon: print("colon"); break;
      case exp: print("exp"); break;
      case proc: print("proc"); break;
      case case_head: print("casehead"); break;
      case record_head: print("recordhead"); break;
      case var_head: print("varhead"); break;
      case elsie: print("elsie"); break;
      case casey: print("casey"); break;
      case mod_scrap: print("module"); break;
      default: print("UNKNOWN"); break;
   }
}
#endif // DEBUG

// 14.2???14.3
// The token lists for translated ???TeX??? output contain some special control symbols as well as ordinary characters.
// These control symbols are interpreted by ???WEAVE??? before they are written to the output file.
// ???	???break_space??? denotes an optional line break or an en space;
// ???	???force??? denotes a line break;
// ???	???big_force??? denotes a line break with additional vertical space;
// ???	???opt??? denotes an optional line break (with the continuation line indented two ems with respect to the normal starting position) ???-
//	this code is followed by an int n, and the break will occur with penalty $10n$;
// ???	???backup??? denotes a backspace of one em;
// ???	???cancel??? obliterates any ???break_space??? or ???force??? or ???big_force??? tokens that immediately precede or follow it
//	and also cancels any ???backup??? tokens that follow it;
// ???	???indent??? causes future lines to be indented one more em;
// ???	???outdent??? causes future lines to be indented one less em.
// All of these tokens are removed from the ???TeX??? output that comes from ???Pas??? text between ???pb??? signs;
// ???break_space??? and ???force??? and ???big_force??? become single spaces in this mode.
// The translation of other ???Pas??? texts results in ???TeX??? control sequences ???\1???, ???\2???, ???\3???, ???\4???, ???\5???, ???\6???, ???\7???
// corresponding respectively to ???indent???, ???outdent???, ???opt???, ???backup???, ???break_space???, ???force???, and ???big_force???.
// However, a sequence of consecutive ?????? ??????, ???break_space???, ???force???, and/or ???big_force??? tokens
// is first replaced by a single token (the maximum of the given ones).

// The tokens ???math_rel???, ???math_bin???, ???math_op??? will be translated into ???\mathrel{???, ???\mathbin{???, and ???\mathop{???, respectively.
// Other control sequences in the ???TeX??? output will be
//	??????\\{??? ??? ???}?????? surrounding identifiers,
//	??????\&{??? ??? ???}?????? surrounding reserved words,
//	??????\.{??? ??? ???}?????? surrounding strings,
//	??????\C{??? ??? ???}??? ???force?????? surrounding comments, and
//	??????\Xn:??? ??? ???\X?????? surrounding module names, where n is the module number.
#define math_bin	0x83		// ???\mathbin{???
#define math_rel	0x84		// ???\mathrel{???
#define math_op		0x85		// ???\mathop{???
#define big_cancel	0x86		// like ???cancel???, also overrides spaces
#define cancel		0x87		// overrides ???backup???, ???break_space???, ???force???, ???big_force???
#define indent		cancel + 1	// one more tab (???\1???)
#define outdent		cancel + 2	// one less tab (???\2???)
#define opt		cancel + 3	// optional break in mid-statement (???\3???)
#define backup		cancel + 4	// stick out one unit to the left (???\4???)
#define break_space	cancel + 5	// optional break between statements (???\5???)
#define force		cancel + 6	// forced break between statements (???\6???)
#define big_force	cancel + 7	// forced break with additional space (???\7???)
#define end_translation	big_force + 1	// special sentinel token at end of list

// 14.3???14.4:
// The raw input is converted into scraps according to the following table, which gives category codes followed by the translations.
// Sometimes a single item of input produces more than one scrap.
// (The symbol ?????????????? stands for ??????\&{????identifier????}??????, i.e., the identifier itself treated as a reserved word.
// In a few cases the category is given as ???comment???; this is not an actual category code,
// it means that the translation will be treated as a comment, as explained below.)
// Editor's Note:
// ???	In the following translation, the categories are listed with their corresponding objects as category Object;
//	the objects in the translations being combinations of objects from the sources and tokens.
// ???	The tokens ???indent???, ???force???, ???big_force???, ???cancel???, ???big_cancel???, ???opt???, ???backup???, ???math_rel??? and ???math_bin???
//	are written respectively as ???, !, ???, x, X, #, -, ??? and +.
// ???	Corresponding to what is denoted by string S in the original, is ??, which was denoted by modified string in the original.
//	???<>???			math???\I???
//	???<=???			math???\L???
//	???>=???			math???\G???
//	???:=???			math???\K???
//	???==???			math???\S???
//	???(*???			math???\B???
//	???*)???			math???\T???
//	???(.???			open???[???
//	???.)???			close???]???
//	???"??? string???S??? ???"???	simp???\.{"??"}???
//	???'??? string???S??? ???'???	simp???\.{'??'}???
//	???@=??? string???S??? ???@>???	simp???\={??}???
//	???#???			math???#???
//	???$???			math???$???
//	???_???			math???_???
//	???%???			math???%???
//	???^???			math???^???
//	???(???			open???(???
//	???)???			close???)???
//	???[???			open???[???
//	???]???			close???]???
//	???*???			math???*???
//	???,???			math???,#9???
//	???..???			math?????????
//	???.???			simp???.???
//	???:???			colon???:???
//	???;???			semi???;???
//	identifier???I???		simp???\{I}???
//	???E??? in constant		exp???\E{???
//	digit???D???		simp???D???
//	other character???C???	math???C???
//	???and???			math???\W???
//	???array???			alpha????????
//	???begin???			beginning???!??x???	intro??????
//	???case???			casey??????		alpha???!?????
//	???const???			intro???!-?????
//	???div???			math???+??}???
//	???do???			omega????????
//	???downto???		math????????}???
//	???else???			terminator??????	elsie???!-?????
//	???end???			terminator??????	close???!?????
//	???file???			alpha????????
//	???for???			alpha???!?????
//	???function???		proc???!-??x???	intro??????\ ???
//	???goto???			intro????????
//	???if???			cond??????		alpha???!?????
//	???in???			math???\in???
//	???label???			intro???!-?????
//	???mod???			math???+??}???
//	???nil???			simp????????
//	???not???			math???\R???
//	???of???			omega????????
//	???or???			math???\V???
//	???packed???		intro????????
//	???procedure???		proc???!-??x???	intro??????\ ???
//	???program???		proc???!-??x???	intro??????\ ???
//	???record???		record_head????????	intro??????
//	???repeat???		beginning???!?????x???	intro??????
//	???set???			alpha????????
//	???then???			omega????????
//	???to???			math????????}???
//	???type???			intro???!-?????
//	???until???			terminator??????	close???!-?????	clause??????
//	???var???			var_head???!-??x???	intro??????
//	???while???			alpha???!?????
//	???with???			alpha???!?????
//	???xclause???		alpha???!\~???	omega????????
//	???@'??? const???K???		simp???\O{K}???
//	???@"??? const???K???		simp???\H{K}???
//	???@$???			simp???\)???
//	???@\???			simp???\]???
//	???@,???			math???\,???
//	???@t??? stuff???S??? ???@>???	simp???S???
//	???@<??? module???M??? ???@>???	mod_scrap???\Xn:M\X???
//	???@#???			comment?????????
//	???@/???			comment???!???
//	???@|???			simp???#0???
//	???@+???			comment???X\ X???
//	???@;???			semi??????
//	???@&???			math???\J???
//	???@{???			math???\B???
//	???@}???			math???\T???
// When a string is output, certain characters are preceded by ??????\?????? signs so that they will print properly.

// A comment in the input will be combined with the preceding omega or semi scrap, or with the following terminator scrap, if possible;
// otherwise it will be inserted as a separate terminator scrap.
// An additional ???comment??? is effectively appended at the end of the ???Pas??? text, just before translation begins;
// this consists of a ???cancel??? token in the switch (of ???Pas??? text in ???pb???, otherwise it consists) of a ???force??? token.

// From this table it is evident that ???WEAVE??? will parse a lot of non-???Pas??? programs.
// For example, the reserved words ??????for?????? and ??????array?????? are treated in an identical way by ???WEAVE??? from a syntactic standpoint,
// and semantically they are equivalent except that a forced line break occurs just before ???????for???????;
// ???Pas??? programmers may well be surprised at this similarity.
// The idea is to keep ???WEAVE???'s rules as simple as possible, consistent with doing a reasonable job on syntactically correct ???Pas??? programs.
// The production rules below have been formulated in the same spirit of ???almost anything goes.???

// 14.4???14.5:
// Here is a table of all the productions.

// The reader can best get a feel for how they work by trying them out by hand on small examples;
// no amount of explanation will be as effective as watching the rules in action.
// Parsing can also be watched by debugging with ??????@2??????.

// Editor's Note:
// ???	In the following translation, the categories are listed with their corresponding objects as category Object;
//	the objects in the translations being combinations of objects from the sources and tokens.
// ???	The tokens ???indent???, ???outdent???, ???force???, ???cancel???, ???opt???, ???break_space???, ???backup??? and ???math_op???
//	are written respectively as ???, ???, !, x, #, ??, - and o.

// #	Production categories			??? translations		Remarks
// 1	alpha A math M colon :			??? alpha A math M:	e.g., switch (v:bool) {
// 2	alpha A math M omega O			??? clause A $M$ ???O	e.g., while (x > 0)
// 3	alpha A omega O				??? clause A ???O		e.g., file of
// 4	alpha A simp S				??? alpha A math S	convert to math mode
// 5	beginning b close q stmt S		??? stmt bqS		compound statement ends
//  	beginning b close q terminator d	??? stmt bqd		compound statement ends
// 6	beginning b stmt S			??? beginning b??S		compound statement grows
// 7	case_head H casey K clause C		??? case_head H???KC	variant records
// 8	case_head H close q terminator d	??? stmt Hx???qd		end of case statement
// 9	case_head H stmt S			??? case_head H!S		case statement grows
// 10	casey K clause C			??? case_head KC		beginning of case statement
// 11	clause C stmt S				??? stmt C??Sx???!	 	end of controlled statement
// 12	cond B clause C stmt S elsie E		??? clause BC??SE x 	complete conditional
// 13	cond B clause C stmt S			??? stmt BC??Sx???!	 	incomplete conditional
// 14	elsie E					??? intro E	 	unmatched else
// 15	exp E math M simp S			??? math EMS}	 	signed exponent ??? where S is not followed by another simp
// 16	exp E simp S				??? math ES}	 	unsigned exponent ??? where S is not followed by another simp
// 17	intro I stmt S				??? stmt I #7xS	 	labeled statement, etc.
// 18	math M close q				??? stmt $M$ close q 	end of field list
// 19	math M colon :				??? intro !-$M$:	 	compound label
// 20	math M??? math M???				??? math M???M???	 	simple concatenation
// 21	math M simp S				??? math M S	 	simple concatenation
// 22	math M stmt S				??? stmt $M$?????Sx???! 	macro or type definition
// 23	math M terminator d			??? stmt $M$d	 	statement involving math
// 24	mod_scrap X terminator d		??? stmt Xd!	 	module like a statement
//	mod_scrap X semi d			??? stmt Xd!	 	module like a statement
// 25	mod_scrap X				??? simp X	 	module unlike a statement
// 26	open p case_head H close q		??? math p$xHx???$q 	case in field list
// 27	open p close q				??? math p\,q	 	empty set []
// 28	open p math M case_head H close q	??? math pM$xHx???$q 	case in field list
// 29	open p math M close q			??? math pMq	 	parenthesized group
// 30	open p math M colon :			??? open p math M: 	colon in parentheses
// 31	open p math M proc Z intro I		??? open p math MoxZ} 	procedure in parentheses
// 32	open p math M semi d			??? open p math Md\,#5 	semicolon in parentheses
// 33	open p math M var_head V intro I	??? open p math MoxV}	var in parentheses
// 34	open p proc Z intro I			??? open p math oxZ}	procedure in parentheses
// 35	open p simp S				??? open p math S		convert to math mode
// 36	open p stmt S close q			??? math p$xSx$q		field list
// 37	open p var_head V intro I		??? open p math oxV}	var in parentheses
// 38	proc Z beginning b close q terminator d	??? stmt Zx???bqd		end of procedure declaration
// 39	proc Z stmt S				??? proc Z??S		procedure declaration grows
// 40	record_head R intro I casey C		??? casey RI xC		????record case???? ???
// 41	record_head R				??? case_head ???Rx		other ????record???? structures
// 42	semi d					??? terminator d		semicolon after statement
// 43	simp S close q				??? stmt S close q	end of field list
// 44	simp S colon :				??? intro !-S:		simple label
// 45	simp S math M				??? math SM		simple concatenation
// 46	simp S mod_scrap X			??? mod_scrap SX		in emergencies
// 47	simp S??? simp S???				??? simp S???S???		simple concatenation
// 48	simp S terminator d			??? stmt Sd		simple statement
// 49	stmt S??? stmt S???				??? stmt S?????S???		adjacent statements
// 50	terminator d				??? stmt d		empty statement
// 51	var_head V beginning b			??? stmt V beginning b	end of variable declarations
// 52	var_head V math M colon :		??? var_head V intro $M$:	variable declaration
// 53	var_head V simp S colon :		??? var_head V intro S:	variable declaration
// 54	var_head V stmt S			??? var_head V??S		variable declarations grow
// 14.5???

// ??15. Implementing the Productions.
// ???15.1: Globals in the outer block (24/34)
// When ???Pas??? text is to be processed with the grammar above, we put its initial scraps $s_1??? s_n$ into two arrays cat[1..n] and trans[1..n].
// The value of cat[k] is simply a category code from the list above; the value of trans[k] is a text pointer, i.e., an index into tok_start.
// Our production rules have the nice property that the right-hand side is never longer than the left-hand side.
// Therefore it is convenient to use sequential allocation for the current sequence of scraps.
// Five pointers are used to manage the parsing:
// ???	pp (the parsing pointer) is such that we are trying to match the category codes cat[pp] cat[pp + 1] ??? to the left-hand sides of productions.
// ???	scrap_base, lo_ptr, hi_ptr, and scrap_ptr are such that the current sequence of scraps appears
//	in positions scrap_base through lo_ptr and hi_ptr through scrap_ptr, inclusive, in the cat and trans arrays.
//	Scraps located between scrap_base and lo_ptr have been examined,
//	while those in positions ??? hi_ptr have not yet been looked at by the parsing process.
// Initially scrap_ptr is set to the position of the final scrap to be parsed, and it doesn't change its value.
// The parsing process makes sure that lo_ptr ??? pp + 3, since productions have as many as four terms, by moving scraps from hi_ptr to lo_ptr.
// If there are fewer than pp + 3 scraps left, the positions up to pp + 3 are filled with blanks that will not match in any productions.
// Parsing stops when pp ??? lo_ptr + 1 and hi_ptr ??? scrap_ptr + 1.

// The trans array elements are declared to be of type enum {0x2800} instead of type text_pointer,
// because the final sorting phase of ???WEAVE??? uses this array to contain elements of type name_pointer.
// Both of these types are subranges of enum {0x2800}.
eight_bits cat[0..max_scraps];		// category codes of scraps
enum {0x2800} trans[0..max_scraps];	// translation texts of scraps
enum {0..max_scraps} pp;		// current position for reducing productions
// ???15.2: Set initial values (16/20)
enum {0..max_scraps} scrap_base ??? 1;	// beginning of the current scrap sequence
enum {0..max_scraps} scrap_ptr ??? 0;	// ending of the current scrap sequence
// 15.2???
enum {0..max_scraps} lo_ptr;		// last scrap that has been examined
enum {0..max_scraps} hi_ptr;		// first scrap that has not been examined
// ???15.2: Set initial values (16/20) [continued]
#if STATS
enum {0..max_scraps} max_scr_ptr ??? 0;	// largest value assumed by scrap_ptr
#endif // STATS
// 15.2???

// 15.1???15.3:
// Token lists in tok_mem are composed of the following kinds of items for ???TeX??? output.
// ???	ASCII codes and special codes like ???force??? and ???math_rel??? represent themselves;
// ???	id_flag + p represents ???\\{????identifier p????}???;
// ???	res_flag + p represents ???\&{????identifier p????}???;
// ???	mod_flag + p represents module name p;
// ???	tok_flag + p represents token list number p;
// ???	inner_tok_flag + p represents token list number p, to be translated without line-break controls.
#define id_flag		0x2800			// signifies an identifier
#define res_flag	id_flag + id_flag	// signifies a reserved word
#define mod_flag	res_flag + id_flag	// signifies a module name
#define tok_flag	mod_flag + id_flag	// signifies a token list
#define inner_tok_flag	tok_flag + id_flag	// signifies a token list in ??????pb??????

#if DEBUG
void print_text(text_pointer p) {	// prints a token list
   if (p ??? text_ptr) print("BAD");
   else for (enum {0..max_toks} j ??? tok_start[p] ??? tok_start[p + 1] - 1) {
      enum {id_flag} r ??? tok_mem[j]%id_flag;		// remainder of token after the flag has been stripped off
      switch (tok_mem[j]/id_flag) {
         case 1: print("\\{"), print_id(r), print("}"); break;	// id_flag
         case 2: print("&{"), print_id(r), print("}"); break;	// res_flag
         case 3: print("<"), print_id(r), print(">"); break;	// mod_flag
         case 4: print("[[%1d]]", r); break;	// tok_flag
         case 5: print("|[[%1d]]|", r); break;	// inner_tok_flag
         default:
      // ???15.4: Print token r in symbolic form
         switch (r) {
            case math_bin: print("\\mathbin{"); break;
            case math_rel: print("\\mathrel{"); break;
            case math_op: print("\\mathop{"); break;
            case big_cancel: print("[ccancel]"); break;
            case cancel: print("[cancel]"); break;
            case indent: print("[indent]"); break;
            case outdent: print("[outdent]"); break;
            case backup: print("[backup]"); break;
            case opt: print("[opt]"); break;
            case break_space: print("[break]"); break;
            case force: print("[force]"); break;
            case big_force: print("[fforce]"); break;
            case end_translation: print("[quit]"); break;
            default: print("%c", xchr[r]); break;
         }
      // 15.4???
         break;
      }
   }
}
#endif // DEBUG

// 15.3???15.5:
// The production rules listed above are embedded directly into the ???WEAVE??? program,
// since it is easier to do this than to write an interpretive system that would handle production systems in general.
// Several macros are defined here so that the program for each production is fairly short.

// All of our productions conform to the general notion that some k consecutive scraps starting at some position j
// are to be replaced by a single scrap of some category c whose translation is composed from the translations of the disappearing scraps.
// After this production has been applied, the production pointer pp should change by an amount d.
// Such a production can be represented by the quadruple (j, k, c, d).
// For example, the production ???simp math ??? math??? would be represented by ???(pp, 2, math, -1)???;
// in this case the pointer $pp$ should decrease by 1 after the production has been applied,
// because some productions with math in their second positions might now match,
// but no productions have math in the third or fourth position of their left-hand sides.
// Note that the value of d is determined by the whole collection of productions, not by an individual one.
// Consider the further example ???var_head math colon ??? var_head intro???, which is represented by ???(pp + 1, 2, intro, +1)???;
// the +1 here is deduced by looking at the grammar and seeing
// that no matches could possibly occur at positions ??? pp after this production has been applied.
// The determination of d has been done by hand in each case, based on the full set of productions
// but not on the grammar of ???Pas??? or on the rules for constructing the initial scraps.

// We also attach a serial number to each production, so that additional information is available when debugging.
// For example, the program below contains the statement ???reduce(pp + 1, 2, intro, +1, 52)??? when it implements the production just mentioned.

// Before calling reduce(), the program should have appended the tokens of the new translation to the tok_mem array.
// We commonly want to append copies of several existing translations, and macros are defined to simplify these common cases.
// For example, appS("%0%1") will append the translations of two consecutive scraps, trans[pp] and trans[pp + 1], to the current token list.
// If the entire new translation is formed in this way, we write ???squash(j, k, c, d)??? instead of ???reduce(j, k, c, d)???.
// For example, ???squash(pp, 2, math, -1)??? is an abbreviation for `appS("%0%1"), reduce(pp, 2, math, -1)'.

// The code below is an exact translation of the production rules into ???Pas???, using such macros,
// and the reader should have no difficulty understanding the format by comparing the code with the symbolic productions as they were listed earlier.
#define app(A) tok_mem[tok_ptr???] ??? A	// this is like app_tok, but it doesn't test for overflow
#define app1(A) tok_mem[tok_ptr???] ??? tok_flag + trans[A]

inline void appS(char *A, ...) {
   va_list AP; va_start(AP, A);
   for (; *A ??? '\0'; A???) {
      ASCII_code Ch = *A;
      if (Ch ??? '%') switch (Ch = *???A) {
         case '0': app1(pp); continue;
         case '1': app1(pp + 1); continue;
         case '2': app1(pp + 2); continue;
         case '3': app1(pp + 3); continue;
         case '\0': A???, Ch = '%'; break;
         case 'c': Ch = va_arg(AP, ASCII_code); break;
         case '<': app(indent); continue;
         case '>': app(outdent); continue;
         case '!': app(force); continue;
         case 'x': app(cancel); continue;
         case 'X': app(big_cancel); continue;
         case '#': app(opt); continue;
         case ':': app(break_space); continue;
         case '-': app(backup); continue;
         case 'o': app(math_op); continue;
         case 'r': app(res_flag + va_arg(AP, name_pointer)); continue;
         case '=': app(math_rel); continue;
         case '+': app(math_bin); continue;
      }
      app(Ch);
   }
   va_end(AP);
}

// Editor's Notes:
// ???	The macros reduce() and squash() of the original have been combined with their respective routines red() and sq() below,
//	with the results given the names of the macros.
// ???	The prod() routine ??? which was originally part of each macro ??? was put into the BumpUpPP() macro
//	in the revised red()/reduce() and sq()/squash() routines.

// 15.5???15.28:
// The ???freeze_text()??? macro is used to give official status to a token list.
// Before saying freeze_text(), items are appended to the current token list,
// and we know that the eventual number of this token list will be the current value of text_ptr.
// But no list of that number really exists as yet, because no ending point for the current list has been stored in the tok_start array.
// After saying freeze_text(), the old current token list becomes legitimate,
// and its number is the current value of text_ptr - 1 since text_ptr has been increased.
// The new current token list is empty and ready to be appended to.
// Note that freeze_text() does not check to see that text_ptr hasn't gotten too large, since it is assumed that this test was done beforehand.
#define freeze_text() (tok_start[???text_ptr] ??? tok_ptr)

// 15.28???15.29:
// This is the code for productions that used to make the appropriate changes to the scrap list.
void reduce(sixteen_bits j, eight_bits k, eight_bits c, int d, eight_bits n) {
   cat[j] ??? c, trans[j] ??? text_ptr, freeze_text();
   if (k > 1) {
      for (enum {0..max_scraps} i0 ??? j + k, i1 ??? j + 1; i0 ??? lo_ptr; i0???, i1???) cat[i1] ??? cat[i0], trans[i1] ??? trans[i0];
      lo_ptr -= k - 1;
   }
   prod(d, n);
}

// 15.29???15.31:
// This procedure is appS("%0%1...%(k-1)"), reduce(...), but takes advantage of the simplification that occurs when k ??? 1.
void squash(sixteen_bits j, eight_bits k, eight_bits c, int d, eight_bits n) {
   for (enum {0..max_scraps} i ??? j; i < j + k; i???) app1(i);
   cat[j] ??? c;
   if (k > 1) {
      trans[j] ??? text_ptr, freeze_text();
      for (enum {0..max_scraps} i0 ??? j + k, i1 ??? j + 1; i0 ??? lo_ptr; i0???, i1???) cat[i1] ??? cat[i0], trans[i1] ??? trans[i0];
      lo_ptr -= k - 1;
   }
   prod(d, n);
}

// 15.31???15.34: Globals in the outer block (25/34)
// If ???WEAVE??? is being run in debugging mode, the production numbers and current stack categories will be printed out when tracing is set to 2;
// a sequence of two or more irreducible scraps will be printed out when tracing is set to 1.
#if DEBUG
// ???20.2: Set initial values (20/20)
enum {3} tracing ??? 0;	// can be used to show parsing details
// 20.2???
#endif // DEBUG

// 15.34???15.35:
// The prod() procedure is called just after reduce() or squash();
// It bumps pp up to ???(scrap_base, pp + d) and ??? in debugging mode ??? displays the number of the production that has just been applied.
void prod(int d, eight_bits n) {
// ???15.30: Change pp to ???(scrap_base, pp + d)
   if (pp + d ??? scrap_base) pp += d; else pp ??? scrap_base
// 15.30???
#if DEBUG
// Show the current categories.
   if (tracing ??? 2) {
      print("\n%1d:", n);
      for (enum {1..max_scraps} k ??? scrap_base ??? lo_ptr) print(k ??? pp? "*": " "), print_cat(cat[k]);
      if (hi_ptr ??? scrap_ptr) print("...");	// indicate that more is coming
   }
#endif // DEBUG
}

// 15.35???15.36:
// The translate() function assumes that scraps have been stored in positions scrap_base through scrap_ptr of cat and trans.
// It appends a terminator scrap and begins to apply productions as much as possible.
// The result is a token list containing the translation of the given sequence of scraps.

// After calling translate(), we will have text_ptr + 3 ??? max_texts and tok_ptr + 6 ??? max_toks,
// so it will be possible to create up to three token lists with up to six tokens without checking for overflow.
// Before calling translate(), we should have text_ptr < max_texts and scrap_ptr < max_scraps,
// since translate() might add a new text and a new scrap before it checks for overflow.

// ???15.7: Declaration of the subprocedure for translate()
void translate_cases(void) {
   switch (cat[pp]) {
      case beginning: switch (cat[pp + 1]) {
      // ???15.9: Cases for beginning
         case close: switch (cat[pp + 2]) {
            case terminator: case stmt: squash(pp, 3, stmt, -2, 5); return;
         }
         break;
         case stmt: appS("%0%:%1"), reduce(pp, 2, beginning, -1, 6); return;
      // 15.9???
      }
      break;
      case intro: switch (cat[pp + 1]) {
      // ???15.16: Cases for intro
         case stmt: appS("%0 %#7%x%1"), reduce(pp, 2, stmt, -2, 17); return;
      // 15.16???
      }
      break;
      case math: switch (cat[pp + 1]) {
      // ???15.17: Cases for math
         case close: appS("$%0$"), reduce(pp, 1, stmt, -2, 18); return;
         case colon: appS("%!%-$%0$%1"), reduce(pp, 2, intro, -3, 19); return;
         case math: squash(pp, 2, math, -1, 20); return;
         case simp: squash(pp, 2, math, -1, 21); return;
         case stmt: appS("$%0$%<%:%1%x%>%!"), reduce(pp, 2, stmt, -2, 22); return;
         case terminator: appS("$%0$%1"), reduce(pp, 2, stmt, -2, 23); return;
      // 15.17???
      }
      break;
      case open: switch (cat[pp + 1]) {
      // ???15.19: Cases for open
         case case_head: switch (cat[pp + 2]) {
            case close: appS("%0$%x%1%x%>$%2"), reduce(pp, 3, math, -1, 26); return;
         }
         break;
         case close: appS("%0\\,%1"), reduce(pp, 2, math, -1, 27); return;
         case math: switch (cat[pp + 2]) {
         // ???15.20: Cases for open math
            case case_head: switch (cat[pp + 3]) {
               case close: appS("%0%1$%x%2%x%>$%3"), reduce(pp, 4, math, -1, 28); return;
            }
            break;
            case close: squash(pp, 3, math, -1, 29); return;
            case colon: squash(pp + 1, 2, math, 0, 30); return;
            case proc: switch (cat[pp + 3]) {
               case intro: appS("%1%o%x%2}"), reduce(pp + 1, 3, math, 0, 31); return;
            }
            break;
            case semi: appS("%1%2\\,%#5"), reduce(pp + 1, 2, math, 0, 32); return;
            case var_head: switch (cat[pp + 3]) {
               case intro: appS("%1%o%x%2}"), reduce(pp + 1, 3, math, 0, 33); return;	//(#) A bug in the original, 31 was listed instead of 33.
            }
            break;
         // 15.20???
         }
         break;
         case proc: switch (cat[pp + 2]) {
            case intro: appS("%o%x%1}"), reduce(pp + 1, 2, math, 0, 34); return;
         }
         break;
         case simp: squash(pp + 1, 1, math, 0, 35); return;
         case stmt: switch (cat[pp + 2]) {
            case close: appS("%0$%x%1%x$%2"), reduce(pp, 3, math, -1, 36); return;
         }
         break;
         case var_head: switch (cat[pp + 2]) {
            case intro: appS("%o%x%1}"), reduce(pp + 1, 2, math, 0, 37); return;
         }
         break;
      // 15.19???
      }
      break;
      case simp: switch (cat[pp + 1]) {
      // ???15.24: Cases for simp
         case close: squash(pp, 1, stmt, -2, 43); return;
         case colon: appS("%!%-%0%1"), reduce(pp, 2, intro, -3, 44); return;
         case math: squash(pp, 2, math, -1, 45); return;
         case mod_scrap: squash(pp, 2, mod_scrap, 0, 46); return;
         case simp: squash(pp, 2, simp, -2, 47); return;
         case terminator: squash(pp, 2, stmt, -2, 48); return;
      // 15.24???
      }
      break;
      case alpha: switch (cat[pp + 1]) {
      // ???15.8: Cases for alpha
      // Now comes the code that tries to match each production starting with a particular type of scrap.
      // Whenever a match is discovered, the squash() or reduce() macro will cause the appropriate action to be performed, followed by goto found.
         case math: switch (cat[pp + 2]) {
            case colon: squash(pp + 1, 2, math, 0, 1); return;
            case omega: appS("%0 $%1$ %<%2"), reduce(pp, 3, clause, -2, 2); return;
         }
         break;
         case omega: appS("%0 %<%1"), reduce(pp, 2, clause, -2, 3); return;
         case simp: squash(pp + 1, 1, math, 0, 4); return;
      // 15.8???
      }
      break;
      case case_head: switch (cat[pp + 1]) {
      // ???15.10: Cases for case_head
         case casey: switch (cat[pp + 2]) {
            case clause: appS("%0%>%1%2"), reduce(pp, 3, case_head, 0, 7); return;
         }
         break;
         case close: switch (cat[pp + 2]) {
            case terminator: appS("%0%x%>%1%2"), reduce(pp, 3, stmt, -2, 8); return;
         }
         break;
         case stmt: appS("%0%!%1"), reduce(pp, 2, case_head, 0, 9); return;
      // 15.10???
      }
      break;
      case casey: switch (cat[pp + 1]) {
      // ???15.11: Cases for casey
         case clause: squash(pp, 2, case_head, 0, 10); return;
      // 15.11???
      }
      break;
      case clause: switch (cat[pp + 1]) {
      // ???15.12: Cases for clause
         case stmt: appS("%0%:%1%x%>%!"), reduce(pp, 2, stmt, -2, 11); return;
      // 15.12???
      }
      break;
      case cond: switch (cat[pp + 1]) {
      // ???15.13: Cases for cond
         case clause: switch (cat[pp + 2]) {
            case stmt: switch (cat[pp + 3]) {
               case elsie: appS("%0%1%:%2%3 %x"), reduce(pp, 4, clause, -2, 12); return;
               default: appS("%0%1%:%2%x%>%!"), reduce(pp, 3, stmt, -2, 13); return;
            }
         }
         break;
      // 15.13???
      }
      break;
      case elsie:
      // ???15.14: Cases for elsie
         squash(pp, 1, intro, -3, 14);
      // 15.14???
      return;
      case exp: switch (cat[pp + 1]) {
      // ???15.15: Cases for exp
         case math: switch (cat[pp + 2]) {
            case simp: switch (cat[pp + 3]) {
               case simp: break;
               default: appS("%0%1%2}"), reduce(pp, 3, math, -1, 15); return;
            }
            break;
         }
         break;
         case simp: switch (cat[pp + 2]) {
            case simp: break;
            default: appS("%0%1}"), reduce(pp, 2, math, -1, 16); return;
         }
         break;
      // 15.15???
      }
      break;
      case mod_scrap: switch (cat[pp + 1]) {
      // ???15.18: Cases for mod_scrap
         case terminator: case semi: appS("%0%1%!"), reduce(pp, 2, stmt, -2, 24); return;
         default: squash(pp, 1, simp, -2, 25); return;
      // 15.18???
      }
      break;
      case proc: switch (cat[pp + 1]) {
      // ???15.21: Cases for proc
         case beginning: switch (cat[pp + 2]) {
            case close: switch (cat[pp + 3]) {
               case terminator: appS("%0%x%>%1%2%3"), reduce(pp, 4, stmt, -2, 38); return;
            }
            break;
         }
         break;
         case stmt: appS("%0%:%1"), reduce(pp, 2, proc, -2, 39); return;
      // 15.21???
      }
      break;
      case record_head: switch (cat[pp + 1]) {
      // ???15.22: Cases for record_head
         case intro: switch (cat[pp + 2]) {
            case casey: appS("%0%1 %x%2"), reduce(pp, 3, casey, -2, 40); return;
         }
         break;
         default: appS("%<%0%x"), reduce(pp, 1, case_head, 0, 41); return;
      // 15.22???
      }
      break;
      case semi:
      // ???15.23: Cases for semi
         squash(pp, 1, terminator, -3, 42);
      // 15.23???
      return;
      case stmt: switch (cat[pp + 1]) {
      // ???15.25: Cases for stmt
         case stmt: appS("%0%:%1"), reduce(pp, 2, stmt, -2, 49); return;
      // 15.25???
      }
      break;
      case terminator:
      // ???15.26: Cases for terminator
         squash(pp, 1, stmt, -2, 50);
      // 15.26???
      return;
      case var_head: switch (cat[pp + 1]) {
      // ???15.27: Cases for var_head
         case beginning: squash(pp, 1, stmt, -2, 51); return;
         case math: switch (cat[pp + 2]) {
            case colon: appS("$%1$%2"), reduce(pp + 1, 2, intro, +1, 52); return;
         }
         break;
         case simp: switch (cat[pp + 2]) {
            case colon: squash(pp + 1, 2, intro, +1, 53); return;
         }
         break;
         case stmt: appS("%0%:%1"), reduce(pp, 2, var_head, -2, 54); return;
      // 15.27???
      }
      break;
   }
   pp???;	// if no match was found, we move to the right
}
// 15.7???

text_pointer translate(void) {	// converts a sequence of scraps
   pp ??? scrap_base, lo_ptr ??? pp - 1, hi_ptr ??? pp;
// ???15.39: If tracing, print an indication of where we are
#if DEBUG
   if (tracing ??? 2) {
      print("\nTracing after l.%1d:", line), mark_harmless();
      if (loc > 50) {
         print("...");
         for (enum {0..long_buf_size} k ??? loc - 51 ??? loc - 1) print("%c", xchr[buffer[k]]);
      } else for (enum {0..long_buf_size} k ??? loc) print("%c", xchr[buffer[k]]);
   }
#endif // DEBUG
// 15.39???15.32: Reduce the scraps using the productions until no more rules apply
// Here now is the code that applies productions as long as possible.
// It requires two local labels (found and break), as well as a local variable (i).
   while (true) {
   // ???15.33: Make sure the entries cat[pp..(pp + 3)] are defined
   // If we get to the end of the scrap list, category codes equal to zero are stored, since zero does not match anything in a production.
      if (lo_ptr < pp + 3) {
         do {
            if (hi_ptr ??? scrap_ptr) cat[???lo_ptr] ??? cat[hi_ptr], trans[lo_ptr] ??? trans[hi_ptr???];
         } while (hi_ptr ??? scrap_ptr && lo_ptr ??? pp + 3);
         for (enum {1..max_scraps} i ??? lo_ptr + 1 ??? pp + 3) cat[i] ??? 0;
      }
   // 15.33???
      if (tok_ptr + 8 > max_toks || text_ptr + 4 > max_texts) {
#if STATS
         if (tok_ptr > max_tok_ptr) max_tok_ptr ??? tok_ptr;
         if (text_ptr > max_txt_ptr) max_txt_ptr ??? text_ptr;
#endif // STATS
         overflow("token/text");
      }
      if (pp > lo_ptr) break;
   // ???15.6: Match a production at pp, or increase pp if there is no match
   // Let us consider the big case statement for productions now, before looking at its context.
   // We want to design the program so that this case statement works,
   // so we might as well not keep ourselves in suspense about exactly what code needs to be provided with a proper environment.
   //
   // The translate() procedure, incorporates the case statement here.
   // Editor's Note:
   // ???	The switch statement was originally separated into smaller pieces, to work around the limitations of ??Pas?? compilers of the time.
   //	The separation was into the cases before, at and after ???alpha???; the portion after being kept in-line.
      translate_cases();
   // 15.6???
   }
// 15.32???
   if (lo_ptr ??? scrap_base && cat[lo_ptr] ??? math) return trans[lo_ptr];
   else {
   // ???15.37: Combine the irreducible scraps that remain
   // If the initial sequence of scraps does not reduce() to a single scrap, we concatenate the translations of all remaining scraps,
   // separated by blank spaces, with dollar signs surrounding the translations of math scraps.
   // ???15.38: If semi-tracing, show the irreducible scraps
#if DEBUG
      if (lo_ptr > scrap_base && tracing ??? 1) {
         print("\nIrreducible scrap sequence in section %1d:\n", module_count); mark_harmless();
         for (enum {0..max_scraps} j ??? scrap_base ??? lo_ptr)  print(" "), print_cat(cat[j]);
      }
#endif // DEBUG
   // 15.38???
      for (enum {0..max_scraps} j ??? scrap_base ??? lo_ptr) {
         if (j ??? scrap_base) app(' ');
         if (cat[j] ??? math) app('$');
         app1(j);
         if (cat[j] ??? math) app('$');
         if (tok_ptr + 6 > max_toks) overflow("token");
      }
      freeze_text();
      return text_ptr - 1;
   // 15.37???
   }
}
// 15.36???

// ??16. Initializing the Scraps.
// ???16.1:
// If we are going to use the powerful production mechanism just developed, we must get the scraps set up in the first place, given a ???Pas??? text.
// A table of the initial scraps corresponding to ???Pas??? tokens appeared above in the section on parsing; our goal now is to implement that table.
// We shall do this by implementing a subroutine called Pascal_parse() that is analogous to the Pascal_xref() routine used during phase one.

// Like Pascal_xref(), the Pascal_parse() procedure starts with the current value of next_control
// and it uses the operation next_control ??? get_next() repeatedly to read ???Pas??? text until encountering the next ??????|?????? or ??????{??????,
// or until next_control ??? format.
// The scraps corresponding to what it reads are appended into the cat and trans arrays, and scrap_ptr is advanced.

// Editor's Note:
// ???	Like prod(), the switch statement in this procedure was originally separated into smaller pieces.
//	The separation was of ???easy cases??? and ???simple cases??? into procedures named easy_cases() and sub_cases() respectively.

// After studying Pascal_parse(), we will look at the sub-procedures app_comment(), app_octal(), and app_hex() that are used in some of its branches.

// ???16.13: Declaration of the app_comment() procedure
// A comment is incorporated into the previous scrap if that scrap is of type omega or semi or terminator.
// (These three categories have consecutive category codes.) Otherwise the comment is entered as a separate scrap of type terminator,
// and it will combine with a terminator scrap that immediately follows it.

// The app_comment() procedure takes care of placing a comment at the end of the current scrap list.
// When app_comment() is called, we assume that the current token list is the translation of the comment involved.
void app_comment(void) {	// append a comment to the scrap list
   freeze_text();
   if (scrap_ptr < scrap_base || cat[scrap_ptr] < omega || cat[scrap_ptr] > terminator) sc0(terminator);
   else app1(scrap_ptr);	// cat[scrap_ptr] is omega or semi or terminator
   app(text_ptr - 1 + tok_flag), trans[scrap_ptr] ??? text_ptr, freeze_text();
}

// 16.13???16.14: Declaration of the app_octal() and app_hex() procedures
// We are now finished with Pascal_parse(), except for two relatively trivial subprocedures that convert constants into tokens.
void app_octal(void) {
   appS("\\O{");
   while (buffer[loc] ??? '0' && buffer[loc] ??? '7') app_tok(buffer[loc???]);
   sc1(simp, '}');
}

void app_hex(void) {
   appS("\\H{");
   while (buffer[loc] ??? '0' && buffer[loc] ??? '9' || buffer[loc] ??? 'A' && buffer[loc] ??? 'F') app_tok(buffer[loc???]);
   sc1(simp, '}');
}
// 16.14???

void Pascal_parse(void) {	// creates scraps from ???Pas??? tokens
   while (next_control < format) {
   // ???16.3: Append the scrap appropriate to next_control
   // ???16.5: Make sure that there is room for at least four more scraps, six more tokens, and four more texts
      if (scrap_ptr + 4 > max_scraps || tok_ptr + 6 > max_toks || text_ptr + 4 > max_texts) {
#if STATS
         if (scrap_ptr > max_scr_ptr) max_scr_ptr ??? scrap_ptr;
         if (tok_ptr > max_tok_ptr) max_tok_ptr ??? tok_ptr;
         if (text_ptr > max_txt_ptr) max_txt_ptr ??? text_ptr;
#endif // STATS
         overflow("scrap/token/text");
      }
   // 16.5???
   reswitch:
      switch (next_control) {
         case string: case verbatim:
         // ???16.7: Append a \(string scrap
         // The following code must use app_tok instead of app in order to protect against overflow.
         // Note that tok_ptr + 1 ??? max_toks after app_tok has been used, so another app is legitimate before testing again.
         //
         // Many of the special characters in a string must be prefixed by ??????\?????? so that ???TeX??? will print them properly.
            appS(next_control ??? verbatim? "\\={": "\\.{");
            for (enum {0..long_buf_size} j ??? id_first; j < id_loc; j???) {
               switch (buffer[j]) {
                  case ' ': case '\\': case '#': case '%': case '$': case '^': case '\'': case '`': case '{': case '}': case '~': case '&': case '_': app('\\'); break;
                  case '@':
                     if (buffer[j + 1] ??? '@') j???;
                     else err_print("! Double @ should be used in strings");
                  break;
               }
               app_tok(buffer[j]);
            }
            sc1(simp, '}');
         // 16.7???
         break;
         case identifier:
         // ???16.9: Append an identifier scrap
            name_pointer p ??? id_lookup(normal);	// identifier designator
            switch (ilk[p]) {
            // ???16.10: The simple cases
            // The simple cases also result in straightforward scraps.
               case normal: sc1(simp, id_flag + p); break;	// not a reserved word
               case array_like: scS(alpha, "%r", p); break;	// ????array????, ????file????, ????set????
               case const_like: scS(intro, "%!%-%r", p); break;	// ????const????, ????label????, ????type????
               case div_like: scS(math, "%+%r}", p); break;	// ????div????, ????mod????
               case do_like: scS(omega, "%r", p); break;	// ????do????, ????of????, ????then????
               case for_like: scS(alpha, "%!%r", p); break;	// ????for????, ????while????, ????with????
               case goto_like: scS(intro, "%r", p); break;	// ????goto????, ????packed????
               case nil_like: scS(simp, "%r", p); break;	// ????nil????
               case to_like: scS(math, "%=%r}", p); break;	// ????downto????, ????to????
            // 16.10???16.11: Cases that generate more than one scrap
               case begin_like: scS(beginning, "%!%r%x", p), sc0(intro); break;	// ????begin????
               case case_like: sc0(casey), scS(alpha, "%!%r", p); break;	// ????case????
               case else_like: appTerm(), scS(elsie, "%!%-%r", p); break;	// ?? else????
               case end_like: appTerm(), scS(close, "%!%r", p); break;	// ????end????
               case if_like: sc0(cond), scS(alpha, "%!%r", p); break;	// ????if????
               case loop_like: scS(alpha, "%!\\~"), scS(omega, "%r", p); break;	// ????xclause????
               case proc_like: scS(proc, "%!%-%r%x", p), scS(intro, "%<\\ "); break;	// ????function????, ????procedure????, ????program????
               case record_like: scS(record_head, "%r", p), sc0(intro); break;	// ????record????
               case repeat_like: scS(beginning, "%!%<%r%x", p), sc0(intro); break;	// ????repeat????
               case until_like: appTerm(), scS(close, "%!%-%r", p), sc0(clause); break;	// ????until????
               case var_like: scS(var_head, "%!%-%r%x", p), sc0(intro); break;	// ????var????
            // 16.11???
               default:
                  next_control ??? ilk[p] - char_like;
               goto reswitch;	// ????and????, ????in????, ????not????, ????or????
            }
         // 16.9???
         break;
         case TeX_string:
         // ???16.8: Append a ???TeX??? string scrap
            appS("\\hbox{");
            for (enum {0..long_buf_size} j ??? id_first ??? id_loc - 1) app_tok(buffer[j]);
            sc1(simp, '}');
         // 16.8???
         break;
      // ???16.4: The easy cases
      // The easy cases each result in straightforward scraps.
         case set_element_sign: scS(math, "\\in"); break;
         case double_dot: scS(math, "\\to"); break;
         case '#': scS(math, "\\#"); break;
         case '$': scS(math, "\\$"); break;
         case '%': scS(math, "\\%"); break;
         case '^': scS(math, "\\^"); break;
         case '_': scS(math, "\\_"); break;
         case ignore: case '|': case xref_roman: case xref_wildcard: case xref_typewriter: break;
         case '(': case '[': sc1(open, next_control); break;
         case ')': case ']': sc1(close, next_control); break;
         case '*': scS(math, "\\ast"); break;
         case ',': scS(math, ",%#9"); break;
         case '.': case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9': sc1(simp, next_control); break;
         case ';': sc1(semi, ';'); break;
         case ':': sc1(colon, ':'); break;
      // ???16.6: Cases involving nonstandard ASCII characters
      // Some nonstandard ASCII characters may have entered ???WEAVE??? by means of standard ones.
      // They are converted to ???TeX??? control sequences so that it is possible to keep ???WEAVE??? from stepping beyond standard ASCII.
         case not_equal: scS(math, "\\I"); break;
         case less_or_equal: scS(math, "\\L"); break;
         case greater_or_equal: scS(math, "\\G"); break;
         case equivalence_sign: scS(math, "\\S"); break;
         case and_sign: scS(math, "\\W"); break;
         case or_sign: scS(math, "\\V"); break;
         case not_sign: scS(math, "\\R"); break;
         case left_arrow: scS(math, "\\K"); break;
      // 16.6???
         case exponent: scS(exp, "\\E{"); break;
         case begin_comment: scS(math, "\\B"); break;
         case end_comment: scS(math, "\\T"); break;
         case octal: app_octal(); break;
         case hex: app_hex(); break;
         case check_sum: scS(simp, "\\)"); break;
         case force_line: scS(simp, "\\]"); break;
         case thin_space: scS(math, "\\,"); break;
         case math_break: scS(simp, "%#0"); break;
         case line_break: comment_scrap(force); break;
         case big_line_break: comment_scrap(big_force); break;
         case no_line_break: appS("%X\\ "), comment_scrap(big_cancel); break;
         case pseudo_semi: sc0(semi); break;
         case join: scS(math, "\\J"); break;
         default: sc1(math, next_control); break;
      // 16.4???
      }
   // 16.3???
      next_control ??? get_next();
      if (next_control ??? '|' || next_control ??? '{') return;
   }
}

// 16.1???16.2:
// The macros defined here are helpful abbreviations for the operations needed when generating the scraps.
// A scrap of category A whose translation has three tokens pp, pp + 1, pp + 2 is generated by scS(A, "%0%1%2"), etc.
#define scS(A, S, ...) (appS(S, ...), cat[???scrap_ptr] ??? A, trans[scrap_ptr] ??? text_ptr, freeze_text())
#define sc1(A, B) (app(B), cat[???scrap_ptr] ??? A, trans[scrap_ptr] ??? text_ptr, freeze_text())
#define sc0(A) (cat[???scrap_ptr] ??? A, trans[scrap_ptr] ??? 0)
#define comment_scrap(A) (app(A), app_comment())

// 16.2???16.12: Append terminator if not already present
// If a comment or semicolon appears before the reserved words ????end????, ?? else????, or ????until????,
// the semi or terminator scrap that is already present overrides the terminator scrap belonging to this reserved word.
inline void appTerm(void) {
   if (scrap_ptr < scrap_base || cat[scrap_ptr] ??? terminator && cat[scrap_ptr] ??? semi) sc0(terminator)
}

// 16.12???16.15:
// When the ??????|?????? that introduces ???Pas??? text is sensed, a call on Pascal_translate()
// will return a pointer to the ???TeX??? translation of that text.
// If scraps exist in the cat and trans arrays, they are unaffected by this translation process.
text_pointer Pascal_translate(void) {
   enum {0..max_scraps} save_base ??? scrap_base;	// holds original value of scrap_base
   scrap_base ??? scrap_ptr + 1;
   Pascal_parse();	// get the scraps together
   if (next_control ??? '|') err_print("! Missing '|' after Pascal text");
   app_tok(cancel), app_comment();	// place a ???cancel??? token as a final ???comment???
   text_pointer p ??? translate();	// make the translation
#if STATS
   if (scrap_ptr > max_scr_ptr) max_scr_ptr ??? scrap_ptr;
#endif // STATS
   scrap_ptr ??? scrap_base - 1, scrap_base ??? save_base;	// scrap the scraps
   return p;
}

// 16.15???16.16:
// The outer_parse() routine is to Pascal_parse() as outer_xref() is to Pascal_xref():
// It constructs a sequence of scraps for ???Pas??? text until next_control ??? format.
// Thus, it takes care of embedded comments.
void outer_parse(void) {	// makes scraps from ???Pas??? tokens and comments
   while (next_control < format)
      if (next_control ??? '{') Pascal_parse();
      else {
      // ???16.17: Make sure that there is room for at least seven more tokens, three more texts, and one more scrap
         if (tok_ptr + 7 > max_toks || text_ptr + 3 > max_texts || scrap_ptr ??? max_scraps) {
#if STATS
            if (scrap_ptr > max_scr_ptr) max_scr_ptr ??? scrap_ptr;
            if (tok_ptr > max_tok_ptr) max_tok_ptr ??? tok_ptr;
            if (text_ptr > max_txt_ptr) max_txt_ptr ??? text_ptr;
#endif // STATS
            overflow("token/text/scrap");
         }
      // 16.17???
         appS("\\C{");
         eight_bits bal ??? copy_comment(1);	// brace level in comment
         next_control ??? '|';
         while (bal > 0) {
            text_pointer p ??? text_ptr;	// partial comment
            freeze_text();
            text_pointer q ??? Pascal_translate();	// partial comment; at this point we have tok_ptr + 6 ??? max_toks
            app(tok_flag + p), app(inner_tok_flag + q);
            bal ??? next_control ??? '|'? copy_comment(bal): 0;	// for next_controk ??? '|': an error has been reported
         }
         app(force), app_comment();	// the full comment becomes a scrap
      }
}
// 16.16???

// ??17. Output of Tokens.
// ???17.1:
// So far our programs have only built up multi-layered token lists in ???WEAVE???'s internal memory;
// we have to figure out how to get them into the desired final form.
// The job of converting token lists to characters in the ???TeX??? output file is not difficult, although it is an implicitly recursive process.
// Four main considerations had to be kept in mind when this part of ???WEAVE??? was designed.
// (a)	There are two modes of output:
//		outer mode, which translates tokens like ???force??? into line-breaking control sequences, and
//		inner mode, which ignores them except that blank spaces take the place of line breaks.
// (b)	The ???cancel??? instruction applies to adjacent token or tokens that are output,
//	and this cuts across levels of recursion since ??????cancel?????? occurs at the beginning or end of a token list on one level.
// (c)	The ???TeX??? output file will be semi-readable if line breaks are inserted after the result of tokens like ???break_space??? and ???force???.
// (d)	The final line break should be suppressed, and there should be no ???force??? token output immediately after ??????\Y\\P??????.

// 17.1???17.2: Types in the outer block (7/7)
// The output process uses a stack to keep track of what is going on at different ???levels??? as the token lists are being written out.
// Entries on this stack have three parts:
// ???	end_field is the tok_mem location where the token list of a particular level will }
// ???	tok_field is the tok_mem location from which the next token on a particular level will be read;
// ???	mode_field is the current mode, either inner or outer.
// The current values of these quantities are referred to quite frequently, so they are stored in a separate place instead of in the stack array.
// We call the current values cur_end, cur_tok, and cur_mode.
//
// The global variable stack_ptr tells how many levels of output are currently in progress.
// The end of output occurs when an end_translation token is found, so the stack is never empty except when we first begin the output process.
#define inner 0	// value of mode for ???Pas??? texts within ???TeX??? texts
#define outer 1	// value of mode for ???Pas??? texts in modules

typedef enum {inner..outer} tymode;
typedef struct {
   sixteen_bits end_field;	// ending location of token list
   sixteen_bits tok_field;	// present location within token list
   mode mode_field;		// interpretation of control tokens
} output_state;

// 17.2???17.3: Globals in the outer block (26/34)
#define cur_end cur_state.end_field	// current ending location in tok_mem
#define cur_tok cur_state.tok_field	// location of next output token in tok_mem
#define cur_mode cur_state.mode_field	// current mode of interpretation
#define init_stack() (stack_ptr ??? 0, cur_mode ??? outer)	// do this to initialize the stack

output_state cur_state;	// cur_end, cur_tok, cur_mode
output_state stack[1..stack_size];	// info for non-current levels
enum {0..stack_size} stack_ptr;	// first unused location in the output state stack
// ???17.4: Set initial values (17/20)
#if STATS
enum {0..stack_size} max_stack_ptr ??? 0;	// largest value assumed by stack_ptr
#endif // STATS
// 17.4???

// 17.3???17.5:
// To insert token-list p into the output, the push_level() subroutine is called; it saves the old level of output and gets a new one going.
// The value of cur_mode is not changed.
void push_level(text_pointer p) {	// suspends the current level
   if (stack_ptr ??? stack_size) overflow("stack");
   else {
      if (stack_ptr > 0) stack[stack_ptr] ??? cur_state;	// save cur_end ??? cur_mode
      stack_ptr???;
#if STATS
      if (stack_ptr > max_stack_ptr) max_stack_ptr ??? stack_ptr;
#endif // STATS
      cur_tok ??? tok_start[p]; cur_end ??? tok_start[p + 1];
   }
}

// 17.5???17.6:
// Conversely, the pop_level() routine restores the conditions that were in force when the current level was begun.
// This subroutine will never be called when stack_ptr ??? 1. It is so simple, we declare it as a macro:
#define pop_level() (cur_state ??? stack[???stack_ptr])	// do this when cur_tok reaches cur_end

// 17.6???17.7:
// The get_output() function returns the next byte of output that is not a reference to a token list.
// It returns the values identifier or res_word or mod_name if the next token is to be an identifier (typeset in italics),
// a reserved word (typeset in boldface) or a module name (typeset by a complex routine that might generate additional levels of output).
// In these cases cur_name points to the identifier or module name in question.
#define res_word 0x81	// returned by get_output() for reserved words
#define mod_name 0x80	// returned by get_output() for module names

eight_bits get_output(void) {	// returns the next token of output
   sixteen_bits a;	// current item read from tok_mem
restart:
   while (cur_tok ??? cur_end) pop_level();
   a ??? tok_mem[cur_tok???];
   if (a ??? 0x100) {
      cur_name ??? a%id_flag;
      switch (a/id_flag) {
         case 2: a ??? res_word; break;	// a ??? res_flag + cur_name
         case 3: a ??? mod_name; break;	// a ??? mod_flag + cur_name
         case 4: push_level(cur_name); goto restart;	// a ??? tok_flag + cur_name
         case 5: push_level(cur_name), cur_mode ??? inner; goto restart;	// a ??? inner_tok_flag + cur_name
         default: a ??? identifier; break;	// a ??? id_flag + cur_name
      }
   }
#if DEBUG
   if (trouble_shooting) debug_help();
#endif // DEBUG
   return a;
}

// 17.7???17.8:
// The real work associated with token output is done by make_output().
// This procedure appends an end_translation token to the current token list,
// and then it repeatedly calls get_output() and feeds characters to the output buffer until reaching the end_translation sentinel.
// // It is possible for make_output() to be called recursively, since a module name may include embedded ???Pas??? text;
// however, the depth of recursion never exceeds one level, since module names cannot be inside of module names.

// A procedure called output_Pascal() does the scanning, translation, and output of ???Pas??? text within ??????pb?????? brackets,
// and this procedure uses make_output() to output the current token list.
// Thus, the recursive callaaaa of make_output() actually occurs when make_output() calls output_Pascal() while outputting the name of a module.
void make_output(void);

void output_Pascal(void) {	// outputs the current token list
   sixteen_bits save_tok_ptr ??? tok_ptr, save_text_ptr ??? text_ptr, save_next_control ??? next_control;	// values to be restored
   next_control ??? '|', text_pointer p ??? Pascal_translate();	// translation of the ???Pas??? text
   app(p + inner_tok_flag);
   make_output();	// output the list
#if STATS
   if (text_ptr > max_txt_ptr) max_txt_ptr ??? text_ptr;
   if (tok_ptr > max_tok_ptr) max_tok_ptr ??? tok_ptr;
#endif // STATS
   text_ptr ??? save_text_ptr; tok_ptr ??? save_tok_ptr;	// forget the tokens
   next_control ??? save_next_control;	// restore next_control to original state
}

// 17.8???17.9:
// Here is ???WEAVE???'s major output handler.
void make_output(void) {	// outputs the equivalents of tokens
   eight_bits b;	// next output byte
   enum {0..max_bytes} k, k_limit;	// indices into byte_mem[]
   enum {ww} w;		// row of byte_mem[]
   enum {0..long_buf_size} j;	// index into buffer
   ASCII_code string_delimiter;	// first and last character of string being copied
   enum {0..long_buf_size} save_loc, save_limit;	// loc and limit to be restored
   name_pointer cur_mod_name;	// name of module being output
   mode save_mode;	// value of cur_mode before a sequence of breaks
   app(end_translation);	// append a sentinel
   freeze_text(), push_level(text_ptr - 1);
   while (true) {
      eight_bits a ??? get_output();	// current output byte
   reswitch:
      switch (a) {
         case end_translation: return;
         case identifier: case res_word:
         // ???17.10: Output an identifier
         // An identifier of length one does not have to be enclosed in braces,
         // and it looks slightly better if set in a math-italic font instead of a (slightly narrower) text-italic font.
         // Thus we output ??????\\|?????? but ??????\\{aa}??????.
            outS("\\%c", a ??? identifier? '&': length(cur_name) ??? 1? '|': '\\'); // a ??? identifier means a ??? res_word
            if (length(cur_name) ??? 1) out1(byte_mem[cur_name%ww][byte_start[cur_name]]); else out_name(cur_name);
         // 17.10???
         break;
         case mod_name:
         // ???17.14: Output a module name
         // The remaining part of make_output() is somewhat more complicated.
         // When we output a module name, we may need to enter the parsing and translation routines,
         // since the name may contain ???Pas??? code embedded in ???pb??? constructions.
         // This ???Pas??? code is placed at the end of the active input buffer and the translation process uses the end of the active tok_mem area.
            outS("\\X");
            cur_xref ??? xref[cur_name];
            if (num(cur_xref) ??? def_flag) {
               out_mod(num(cur_xref) - def_flag);
               if (phase_three) {
                  cur_xref ??? xlink(cur_xref);
                  for (; num(cur_xref) ??? def_flag; cur_xref ??? xlink(cur_xref))
                     outS(", "), out_mod(num(cur_xref) - def_flag);
               }
            } else out1('0');	// output the module number, or zero if it was undefined
            out1(':');
         // ???17.15: Output the text of the module name
            k ??? byte_start[cur_name], w ??? cur_name%ww, k_limit ??? byte_start[cur_name + ww];
            cur_mod_name ??? cur_name;
            while (k < k_limit) {
               eight_bits b ??? byte_mem[w][k???];
               if (b ??? '@') {
               // ???17.16: Skip next character, give error if not ??????@??????
                  if (byte_mem[w][k] ??? '@') print("\n! Illegal control code in section name:\n<"), print_id(cur_mod_name), print("> "), mark_error();
                  k???;
               // 17.16???
               }
               if (b ??? '|') out1(b);
               else {
               // ???17.17: Copy the ???Pas??? text into buffer[(limit + 1)..j]
               // The ???Pas??? text enclosed in ???pb??? should not contain ??????|?????? characters, except within strings.
               // We put a ??????|?????? at the front of the buffer, so that an error message that displays the whole buffer will look a little bit sensible.
               // The variable string_delimiter is zero outside of strings, otherwise it equals the delimiter that began the string being copied.
                  j ??? limit + 1, buffer[j] ??? '|', string_delimiter ??? 0;
                  while (true) {
                     if (k ??? k_limit) {
                        print("\n! Pascal text in section name didn't end:\n<"), print_id(cur_mod_name), print("> "), mark_error();
                        break;
                     }
                     eight_bits b ??? byte_mem[w][k???];
                     if (b ??? '@') {
                     // ???17.18: Copy a control code into the buffer
                        if (j > long_buf_size - 4) overflow("buffer");
                        buffer[j???] ??? '@', buffer[j???] ??? byte_mem[w][k???];	//(#) This should be preceded by a range check on k.
                     // 17.18???
                     } else {
                        if (b ??? '"' || b ??? '\'')
                           if (string_delimiter ??? 0) string_delimiter ??? b;
                           else if (string_delimiter ??? b) string_delimiter ??? 0;
                        if (b ??? '|' || string_delimiter ??? 0) {
                           if (j > long_buf_size - 3) overflow("buffer");
                           buffer[???j] ??? b;
                        } else break;
                     }
                  }
               // 17.17???
                  save_loc ??? loc, save_limit ??? limit, loc ??? limit + 2, limit ??? j + 1;
                  buffer[limit] ??? '|', output_Pascal();
                  loc ??? save_loc, limit ??? save_limit;
               }
            }
         // 17.15???
            outS("\\X");
         // 17.14???
         break;
         case math_bin: case math_op: case math_rel:
         // ???17.11: Output a ???\math??? operator
            if (a ??? math_bin) outS("\\mathbin{");
            else if (a ??? math_rel) outS("\\mathrel{");
            else outS("\\mathop{");
         // 17.11???
         break;
         case cancel:
            do a ??? get_output(); while (a ??? backup && a ??? big_force);
         goto reswitch;
         case big_cancel:
            do a ??? get_output(); while ((a ??? backup || a ??? ' ') && a ??? big_force);
         goto reswitch;
         case indent: case outdent: case opt: case backup: case break_space: case force: case big_force:
         // ???17.12: Output a \(control, look ahead in case of line breaks, possibly goto reswitch
         // The current mode does not affect the behavior of ???WEAVE???'s output routine except when we are outputting control tokens.
            if (a < break_space) {
               if (cur_mode ??? outer) {
                  outS("\\%c", a - cancel + '0');
                  if (a ??? opt) out1(get_output());	// ???opt??? is followed by a digit
               } else if (a ??? opt) b ??? get_output();	// ignore digit following ???opt???
            } else {
            // ???17.13: Look ahead for strongest line break
            // If several of the tokens ???break_space???, ???force???, ???big_force??? occur in a row,
            // possibly mixed with blank spaces (which are ignored), the largest one is used.
            // A line break also occurs in the output file, except at the very end of the translation.
            // The very first line break is suppressed (i.e., a line break that follows ??????\Y\P??????).
               b ??? a, save_mode ??? cur_mode;
               while (true) {
                  a ??? get_output();
                  if (a ??? cancel || a ??? big_cancel) break;	// ???cancel??? overrides everything
                  if (a ??? ' ' && a < break_space || a > big_force) {
                     if (save_mode ??? outer) {
                        if (out_ptr > 3)
                           if (out_buf[out_ptr] ??? 'P' && out_buf[out_ptr-1] ??? '\\' && out_buf[out_ptr-2] ??? 'Y' && out_buf[out_ptr-3] ??? '\\')
                              break;
                        outS("\\%c", b - cancel + '0');
                        if (a ??? end_translation) finish_line();
                     } else if (a ??? end_translation && cur_mode ??? inner) out1(' ');
                     break;
                  }
                  if (a > b) b ??? a;	// if a ??? ' ' we have a < b
               }
            // 17.13???
               goto reswitch;
            }
         // 17.12???
         break;
         default:	// otherwise a is an ASCII character
            out1(a);
         break;
      }
   }
}
// 17.9???

// ??18. Phase Two Processing.
// ???18.2: Globals in the outer block (27/34)
// The output file will contain the control sequence ???\Y??? between non-null sections of a module, e.g.,
// between the ???TeX??? and definition parts if both are nonempty.
// This puts a little white space between the parts when they are printed.
// However, we don't want ???\Y??? to occur between two definitions within a single module.
// The variables out_line or out_ptr will change if a section is non-null,
// so the following macros ???save_position()??? and ???emit_space_if_needed()??? are able to handle the situation:
#define save_position() (save_line ??? out_line, save_place ??? out_ptr)
inline void emit_space_if_needed(void) { if (save_line ??? out_line || save_place ??? out_ptr) outS("\\Y"); }

int save_line;			// former value of out_line
sixteen_bits save_place;	// former value of out_ptr
// 18.2???

// ???18.9:
// The finish_Pascal() procedure outputs the translation of the current scraps, preceded by the control sequence ??????\P??????
// and followed by the control sequence ??????\par??????.
// It also restores the token and scrap memories to their initial empty state.

// A ???force??? token is appended to the current scraps before translation takes place,
// so that the translation will normally end with ???\6??? or ???\7??? (the ???TeX??? macros for ???force??? and ???big_force???).
// This ???\6??? or ???\7??? is replaced by the concluding ???\par??? or by ???\Y\par???.
void finish_Pascal(void) {	// finishes a definition or a ???Pas??? part
   outS("\\P"), app_tok(force), app_comment();
   text_pointer p ??? translate();	// translation of the scraps
   app(p + tok_flag), make_output();	// output the list
   if (out_ptr > 1 && out_buf[out_ptr - 1] ??? '\\')
      if (out_buf[out_ptr] ??? '6') out_ptr -= 2;
      else if (out_buf[out_ptr] ??? '7') out_buf[out_ptr] ??? 'Y';
   outS("\\par"), finish_line();
#if STATS
   if (text_ptr > max_txt_ptr) max_txt_ptr ??? text_ptr;
   if (tok_ptr > max_tok_ptr) max_tok_ptr ??? tok_ptr;
   if (scrap_ptr > max_scr_ptr) max_scr_ptr ??? scrap_ptr;
#endif // STATS
   tok_ptr ??? 1, text_ptr ??? 1, scrap_ptr ??? 0;	// forget the tokens and the scraps
}

// 18.9???18.12: Globals in the outer block (28/34)
// Finally, when the ???TeX??? and definition parts have been treated, we have next_control ??? begin_Pascal.
// We will make the global variable this_module point to the current module name, if it has a name.
name_pointer this_module;	// the current module name, or zero
// 18.12???

// ???18.17: Globals in the outer block (29/34)
// To rearrange the order of the linked list of cross references, we need four more variables that point to cross reference entries.
// We'll end up with a list pointed to by cur_xref.
xref_number next_xref, this_xref, first_xref, mid_xref;	// pointer variables for rearranging a list

// 18.17???18.19:
// The footnote() procedure gives cross reference information about multiply defined module names
// (if the flag parameter is def_flag), or about the uses of a module name (if the flag parameter is zero).
// It assumes that cur_xref points to the first cross-reference entry of interest, and it leaves cur_xref pointing to the first element not printed.
// Typical outputs: ??????\A101.??????; ??????\Us370\\ET1009.??????; ??????\As8, 27\\*, 51\\ETs64.??????.
void footnote(sixteen_bits flag) {	// outputs module cross-references
   if (num(cur_xref) ??? flag) return;
   finish_line(), out1('\\');
   out1(flag ??? 0? 'U': 'A');
// ???18.20: Output all the module numbers on the reference list cur_xref
// The following code distinguishes three cases, according as the number of cross references is one, two, or more than two.
// Variable q points to the first cross reference, and the last link is a zero.
   xref_number q ??? cur_xref;	// cross-reference pointer variable
   if (num(xlink(q)) > flag) out1('s');	// plural
   while (true) {
      out_mod(num(cur_xref) - flag);
      cur_xref ??? xlink(cur_xref);	// point to the next cross reference to output
      if (num(cur_xref) ??? flag) break;
      if (num(xlink(cur_xref)) > flag) outS(", ");	// not the last
      else {
         outS("\\ET");	// the last
         if (cur_xref ??? xlink(q)) out1('s');	// the last of more than two
      }
   }
// 18.20???
   out1('.');
}
// 18.19???

// ??19. Phase Three Processing.
// ???19.2: Globals in the outer block (30/34)
// Just before the index comes a list of all the changed modules, including the index module itself.
enum {0..max_modules} k_module;	// runs through the modules

// 19.2???19.4: Globals in the outer block (31/34)
// A left-to-right radix sorting method is used, since this makes it easy to adjust the collating sequence
// and since the running time will be at worst proportional to the total length of all entries in the index.
// We put the identifiers into 230 different lists based on their first characters.
// (Uppercase letters are put into the same list as the corresponding lowercase letters, since we want to have ???t < \{TeX} < ????to???????.)
// The list for character c begins at location bucket[c] and continues through the blink array.
name_pointer bucket[ASCII_code];
name_pointer next_name;			// successor of cur_name when sorting
ASCII_code c;				// index into bucket
enum {0..hash_size} h;			// index into hash
sixteen_bits blink[0..max_names];	// links in the buckets

// 19.4???19.6: Globals in the outer block (32/34)
// During the sorting phase we shall use the cat and trans arrays from ???WEAVE???'s parsing algorithm and rename them depth and head.
// They now represent a stack of identifier lists for all the index entries that have not yet been output.
// The variable sort_ptr tells how many such lists are present; the lists are output in reverse order (first sort_ptr, then sort_ptr - 1, etc.).
// The j'th list starts at head[j], and if the first k characters of all entries on this list are known to be equal we have depth[j] ??? k.
#define depth cat		// reclaims memory that is no longer needed for parsing
#define head trans		// ditto
#define sort_ptr scrap_ptr	// ditto
#define max_sorts max_scraps	// ditto

eight_bits cur_depth;			// depth of current buckets
enum {0..max_bytes} cur_byte;		// index into byte_mem[]
enum {ww} cur_bank;			// row of byte_mem[]
sixteen_bits cur_val;			// current cross reference number
// ???19.7: Set initial values (18/20)
#if STATS
enum {0..max_sorts} max_sort_ptr ??? 0;	// largest value of sort_ptr
#endif // STATS
// 19.7???

// 19.6???19.8: Globals in the outer block (33/34)
// The desired alphabetic order is specified by the collate array; namely, collate[0] < collate[1] < ??? < collate[229].
ASCII_code collate[230];	// collation order

// 19.8???19.11:
// Procedure unbucket() goes through the buckets and adds nonempty lists to the stack, using the collating sequence specified in the collate array.
// The parameter to unbucket() tells the current depth in the buckets.
// Any two sequences that agree in their first 0xff character positions are regarded as identical.
#define infinity 0xff	// $\infty$ (approximately)

void unbucket(eight_bits d) {	// empties buckets having depth d
   for (ASCII_code c ??? 229 ??? 0) if (bucket[collate[c]] > 0) {
      if (sort_ptr > max_sorts) overflow("sorting");
      sort_ptr???;
#if STATS
      if (sort_ptr > max_sort_ptr) max_sort_ptr ??? sort_ptr;
#endif // STATS
      if (c ??? 0) depth[sort_ptr] ??? infinity; else depth[sort_ptr] ??? d;
      head[sort_ptr] ??? bucket[collate[c]]; bucket[collate[c]] ??? 0;
   }
}

// 19.11???19.18:
The following recursive procedure walks through the tree of module names and prints them.
void mod_print(name_pointer p) {	// print all module names in subtree p
   if (p > 0) {
      mod_print(llink[p]);
      outS("\\:");
      tok_ptr ??? 1, text_ptr ??? 1, scrap_ptr ??? 0, init_stack();
      app(p + mod_flag), make_output();
      footnote(0);	// cur_xref was set by make_output()
      finish_line();
      mod_print(rlink[p]);
   }
}
// 19.18???

// ??20. Debugging.
// ???20.1: Globals in the outer block (34/34)
// The ???Pas??? debugger with which ???WEAVE??? was developed allows breakpoints to be set,
// and variables can be read and changed, but procedures cannot be executed.
// Therefore a ???debug_help()??? procedure has been inserted in the main loops of each phase of the program;
// when ddt and dd are set to appropriate values, symbolic printouts of various tables will appear.

// The idea is to set a breakpoint inside the debug_help() routine, at the place of ???breakpoint:??? below.
// Then when debug_help() is to be activated, set trouble_shooting equal to true.
// The debug_help() routine will prompt you for values of ddt and dd, discontinuing this when ddt ??? 0;
// thus you type 2n + 1 integers, ending with zero or a negative number.
// Then control either passes to the breakpoint, allowing you to look at and/or change variables (if you typed zero),
// or to exit the routine (if you typed a negative value).

// Another global variable, debug_cycle, can be used to skip silently past calls on debug_help().
// If you set debug_cycle > 1, the program stops only every debug_cycle times debug_help() is called;
// however, any error stop will set debug_cycle to zero.
#if DEBUG
// ???20.2: Set initial values (20/20) [continued]
bool trouble_shooting ??? true;	// is debug_help() wanted?
// 20.2???
int ddt;		// operation code for the debug_help() routine
int dd;			// operand in procedures performed by debug_help()
// ???20.2: Set initial values (20/20) [continued]
int debug_cycle ??? 1;	// threshold for debug_help() stopping
int debug_skipped ??? 0;	// we have skipped this many debug_help() calls
// 20.2???
text_file term_in;	// the user's terminal as an input file
// trouble_shooting ??? false, debug_cycle ??? 99999;	// use these when it almost works
#endif // DEBUG

// 20.1???20.3:
// #define breakpoint 888	// place where a breakpoint is desirable
// (#) system dependencies
#if DEBUG
void debug_help(void) {	// routine to display various things
   if (???debug_skipped < debug_cycle) return;
   debug_skipped ??? 0;
   while (true) {
      print("\n#"), update_terminal();	// prompt
      read(term_in, ddt);		// read a debug-command code
      if (ddt < 0) return;
      else if (ddt ??? 0) {
         goto breakpoint;		// go to every label at least once
      breakpoint:
         ddt ??? 0;
      } else {
         read(term_in, dd);
         switch (ddt) {
            case 1: print_id(dd); break;
            case 2: print_text(dd); break;
            case 3:
               for (int k ??? 1 ??? dd) print("%c", xchr[buffer[k]]);
            break;
            case 4:
               for (int k ??? 1 ??? dd) print("%c", xchr[mod_text[k]]);
            break;
            case 5:
               for (int k ??? 1 ??? out_ptr) print("%c", xchr[out_buf[k]]);
            break;
            case 6:
               for (int k ??? 1 ??? dd) print_cat(cat[k]), print(" ");
            break;
            default: print("?"); break;
         }
      }
   }
}
#endif // DEBUG
// 20.3???

// ??21. The Main Program.
// ???21.1:
// Let's put it all together now: ???WEAVE??? starts and ends here.
// (#) system dependencies
//
// The main procedure has been split into three sub-procedures in order to keep certain ???Pas??? compilers from overflowing their capacity.
void Phase_I(void) {
// ???11.2: Phase I: Read all the user's text and store the cross references
// The overall processing strategy in phase one has the following straightforward outline.
   phase_one ??? true, phase_three ??? false;
   reset_input();
   module_count ??? 0, skip_limbo(), change_exists ??? false;
   while (!input_has_ended) {
   // ???11.3: Store cross reference data for the current module
      if (???module_count ??? max_modules) overflow("section number");
      changed_module[module_count] ??? changing;	// it will become true if any line changes
      if (buffer[loc - 1] ??? '*') print("*%1d", module_count), update_terminal();	// print a progress report
   // ???11.6: Store cross references in the ???TeX??? part of a module
   // In the ???TeX??? part of a module, cross reference entries are made only for the identifiers in ???Pas??? texts enclosed in ???pb???,
   // or for control texts enclosed in ???@^??? ??? ???@>??? or ???@.??? ??? ???@>??? or ???@:??? ??? ???@>???.
      do {
         next_control ??? skip_TeX();
         switch (next_control) {
            case underline: xref_switch ??? def_flag; break;
            case no_underline: xref_switch ??? 0; break;
            case '|': Pascal_xref(); break;
            case xref_roman: case xref_wildcard: case xref_typewriter: case module_name:
               loc -= 2, next_control ??? get_next();	// scan to ???@>???
               if (next_control ??? module_name) new_xref(id_lookup(next_control - identifier));
            break;
         }
      } while (next_control < format);
   // 11.6???11.8: Store cross references in the \(definition part of a module
   // When we get to the following code we have next_control ??? format.
      while (next_control ??? definition) {format or definition} {
         xref_switch ??? def_flag;	// implied ???@!???
         if (next_control ??? definition) next_control ??? get_next();
         else {
         // ???11.9: Process a format definition
         // Error messages for improper format definitions will be issued in phase two.
         // Our job in phase one is to define the ilk of a properly formatted identifier,
         // and to fool the new_xref() routine into thinking that the identifier on the right-hand side of the format definition is not a reserved word.
            next_control ??? get_next();
            if (next_control ??? identifier) {
               lhs ??? id_lookup(normal), ilk[lhs] ??? normal, new_xref(lhs);
               next_control ??? get_next();
               if (next_control ??? equivalence_sign) {
                  next_control ??? get_next();
                  if (next_control ??? identifier) {
                     rhs ??? id_lookup(normal);
                     ilk[lhs] ??? ilk[rhs], ilk[rhs] ??? normal, new_xref(rhs);
                     ilk[rhs] ??? ilk[lhs], next_control ??? get_next();
                  }
               }
            }
         // 11.9???
         }
         outer_xref();
      }
   // 11.8???11.10: Store cross references in the ???Pas??? part of a module
   // Finally, when the ???TeX??? and definition parts have been treated, we have next_control ??? begin_Pascal.
      if (next_control ??? module_name) {	// begin_Pascal or module_name
         mod_xref_switch ??? next_control ??? begin_Pascal? 0: def_flag;
         do {
            if (next_control ??? module_name) new_mod_xref(cur_module);
            next_control ??? get_next(), outer_xref();
         } while (next_control ??? module_name);
      }
   // 11.10???
      if (changed_module[module_count]) change_exists ??? true;
   // 11.3???
   }
   changed_module[module_count] ??? change_exists;	// the index changes if anything does
   phase_one ??? false;	// prepare for second phase
// ???11.13: Print error messages about unused or undefined module names
   mod_check(root)
// 11.13???
// 11.2???
}

void Phase_II(void) {
// ???18.1: Phase II: Read all the text again and translate it to ???TeX??? form
// We have assembled enough pieces of the puzzle in order to be ready to specify the processing in ???WEAVE???'s main pass over the source file.
// Phase two is analogous to phase one,
// except that more work is involved because we must actually output the ???TeX??? material instead of merely looking at the ???WEB??? specifications.
   reset_input(), print("\nWriting the output file...");
   module_count ??? 0;
   copy_limbo();
   finish_line(), flush_buffer(0, false, false);	// insert a blank line, it looks nice
   while (not input_has_ended) {
   // ???18.3: Translate the \(current module
      module_count???;
   // ???18.4: Output the code for the beginning of a new module
   // Modules beginning with the ???WEB??? control sequence ??????@\ ?????? start in the output with the ???TeX??? control sequence ??????\M??????, followed by the module number.
   // Similarly, ??????@*?????? modules lead to the control sequence ??????\N??????.
   // If this is a changed module, we put ???*??? just before the module number.
      out1('\\');
      if (buffer[loc - 1] ??? '*') out1('M');
      else out1('N'), print("*%1d", module_count), update_terminal();	// print a progress report
      out_mod(module_count), outS(". ")
   // 18.4???
      save_position();
   // ???18.5: Translate the ???TeX??? part of the current module
   // In the ???TeX??? part of a module, we simply copy the source text, except that index entries are not copied and ???Pas??? text within ???pb??? is translated.
      do {
         next_control ??? copy_TeX();
         switch (next_control) {
            case '|': init_stack(), output_Pascal(); break;
            case '@': out1('@'); break;
            case octal:
            // ???18.6: Translate an octal constant appearing in ???TeX??? text
               outS("\\O{");
               while (buffer[loc] ??? '0' && buffer[loc] ??? '7') out1(buffer[loc???]);	// since buffer[limit] ??? ' ', this loop will end
               out1('}');
            // 18.6???
            break;
            case hex:
            // ???18.7: Translate a hexadecimal constant appearing in ???TeX??? text
               outS("\\H{");
               while (buffer[loc] ??? '0' && buffer[loc] ??? '9' || buffer[loc] ??? 'A' && buffer[loc] ??? 'F') out1(buffer[loc???]);
               out1('}');
            // 18.7???
            break;
            case TeX_string: case xref_roman: case xref_wildcard: case xref_typewriter: case module_name: {
               loc -= 2, next_control ??? get_next();	// skip to ???@>???
               if (next_control ??? TeX_string) err_print("! TeX string should be in Pascal text only");
            break;
            case begin_comment: case end_comment: case check_sum: case thin_space: case math_break: case line_break: case big_line_break: case no_line_break: case join: cas: case pseudo_semi:
               err_print("! You can't do that in TeX text");
            break;
         }
      } while (next_control < format);
   // 18.5???18.8: Translate the \(definition part of the current module
   // When we get to the following code we have next_control ??? format, and the token memory is in its initial empty state.
      if (next_control ??? definition)	// definition part non-empty
         emit_space_if_needed(), save_position();
      while (next_control ??? definition) {	//format or definition
         init_stack();
         if (next_control ??? definition) {
         // ???18.10: Start a macro definition
            scS(intro, "\\D");	// this will produce ???????define ???????
            next_control ??? get_next();
            if (next_control ??? identifier) err_print("! Improper macro definition");
            else sc1(id_flag + id_lookup(normal), math);
            next_control ??? get_next();
         // 18.10???
         } else {
         // ???18.11: Start a format definition
            scS(intro, "\\F");	// this will produce ???????format ???????
            next_control ??? get_next();
            if (next_control ??? identifier) {
               sc1(id_flag + id_lookup(normal), math);
               next_control ??? get_next();
               if (next_control ??? equivalence_sign) {
                  scS(math, "\\S");	// output an equivalence sign
                  next_control ??? get_next();
                  if (next_control ??? identifier) {
                     sc1(id_flag + id_lookup(normal), math);
                     sc0(semi);	// insert an invisible semicolon
                     next_control ??? get_next();
                  }
               }
            }
            if (scrap_ptr ??? 5) err_print("! Improper format definition");
         // 18.11???
         }
         outer_parse(), finish_Pascal();
      }
   // 18.8???18.13: Translate the ???Pas??? part of the current module
      this_module ??? 0;
      if (next_control ??? module_name) {
         emit_space_if_needed(), init_stack();
         if (next_control ??? begin_Pascal) next_control ??? get_next();
         else {
            this_module ??? cur_module;
         // ???18.14: Check that = or == follows this module name, and emit the scraps to start the module definition
            do next_control ??? get_next(); while (next_control ??? '+');	// allow optional ??????+=??????
            if (next_control ??? '=' && next_control ??? equivalence_sign) err_print("! You need an = sign after the section name");
            else next_control ??? get_next();
            if (out_ptr > 1 && out_buf[out_ptr] ??? 'Y' && out_buf[out_ptr - 1] ??? '\\') app(backup);	// the module name will be flush left
            sc1(mod_flag + this_module, mod_scrap);
            cur_xref ??? xref[this_module];
            if (num(cur_xref) ??? module_count + def_flag)
               scS(math, "%=+}"),	// module name is multiply defined
               this_module ??? 0;	// so we won't give cross-reference info here
            scS(math, "\\S");	// output an equivalence sign
            sc1(force, semi);	// this forces a line break unless ??????@+?????? follows
         // 18.14???
         }
         while (next_control ??? module_name) {
            outer_parse();
         // ???18.15: Emit the scrap for a module name if present
            if (next_control < module_name) err_print("! You can't do that in Pascal text"), next_control ??? get_next();
            else if (next_control ??? module_name) sc1(mod_flag + cur_module, mod_scrap), next_control ??? get_next();
         // 18.15???
         }
         finish_Pascal();
      }
   // 18.13???18.16: Show cross references to this module
   // Cross references relating to a named module are given after the module ends.
      if (this_module > 0) {
      // ???18.18: Rearrange the list pointed to by cur_xref
      // We want to rearrange the cross reference list so that all the entries with def_flag come first, in ascending order;
      // then come all the other entries, in ascending order.
      // There may be no entries in either one or both of these categories.
         first_xref ??? xref[this_module];
         this_xref ??? xlink(first_xref);	// bypass current module number
         if (num(this_xref) > def_flag) {
            mid_xref ??? this_xref, cur_xref ??? 0;	// this value doesn't matter
            do
               next_xref ??? xlink(this_xref), xlink(this_xref) ??? cur_xref,
               cur_xref ??? this_xref, this_xref ??? next_xref;
            while (num(this_xref) > def_flag);
            xlink(first_xref) ??? cur_xref;
         } else mid_xref ??? 0;	// first list null
         cur_xref ??? 0;
         while (this_xref ??? 0)
            next_xref ??? xlink(this_xref), xlink(this_xref) ??? cur_xref,
            cur_xref ??? this_xref, this_xref ??? next_xref;
         xlink(mid_xref > 0? mid_xref: first_xref) ??? cur_xref;
         cur_xref ??? xlink(first_xref)
      // 18.18???
         footnote(def_flag), footnote(0);
      }
   // 18.16???18.21: Output the code for the end of a module
      outS("\\fi"), finish_line();
      flush_buffer(0, false, false);	// insert a blank line, it looks nice
   // 18.21???
   // 18.3???
   }
// 18.1???
}

int main(int AC, char *AV[]) {
// ???1.2: [continued]
// Initialize global variables
// ???2.8: Set initial values (4/20)
// The following system-independent code makes the xord array contain a suitable inverse to the information in xchr.
   for (enum {0x100} i ??? first_text_char ??? last_text_char) xord[chr(i)] ??? ' ';
   for (enum {0x100} i ??? 0x01 ??? 0xff) xord[xchr[i]] ??? i;
   xord[' '] ??? ' ';
// 2.8???3.3: Set initial values (5/20)
// Different systems have different ways of specifying that the output on a certain file will appear on the user's terminal.
// Here is one way to do this on the ???Pas??? system that was used in ???TANGLE???'s initial development:
// (#) system dependencies
   rewrite(term_out, "TTY:");	// send term_out output to the terminal
// 3.3???3.8: Set initial values (6/20)
// The following code opens tex_file.
// Since this file was listed in the program header, we assume that the ???Pas??? runtime system has checked that a suitable external file name has been given.
// (#) system dependencies
   rewrite(tex_file);
// 3.8???
// (In reference to ???12.3:)
// ???12.4: Set initial values (14/20) [continued]
// In particular, the finish_line() procedure is called near the very beginning of phase two.
// We initialize the output variables in a slightly tricky way so that the first line of the output file will be ??????\input webmac??????.
   out_buf[1] ??? 'c', write(tex_file, "\\input webma");
// 12.4???19.10: Set initial values (19/20)
// We use the order null < ???\??? < other characters < ???_??? < ???A??? ??? ???a??? < ??? < ???Z??? ??? ???z??? < ???0??? < ??? < ???9???.
   collate[0] ??? 0, collate[1] ??? ' ';
   for (ASCII_code c ??? 1 ??? ' ' - 1) collate[c + 1] ??? c;
   for (ASCII_code c ??? ' ' + 1 ??? '0' - 1) collate[c] ??? c;
   for (ASCII_code c ??? '9' + 1 ??? 'A' - 1) collate[c - 10] ??? c;
   for (ASCII_code c ??? 'Z' + 1 ??? '_' - 1) collate[c - 36] ??? c;
   collate['_' - 36] ??? '_' + 1;
   for (ASCII_code c ??? 'z' + 1 ??? 0xff) collate[c - 0x3f] ??? c;
   collate[0xc1] ??? '_';
   for (ASCII_code c ??? 'a' ??? 'z') collate[c - 'a' + 0xc2] ??? c;
   for (ASCII_code c ??? '0' ??? '9') collate[c - '0' + 0xdc] ??? c;
// 19.10???20.2: Set initial values (20/20) [continued]
// The debugging routine needs to read from the user's terminal.
// (#) system dependencies
   reset(term_in, "TTY:", "/I");	// open term_in as the terminal, don"t do a get
// 20.2???
// 1.2???
   print(banner "\n");	// print a ???banner line???
// ???7.2: Store all the reserved words
// The intended use of the macros above might not be immediately obvious, but the riddle is answered by the following:
   id_loc ??? 10;
   id(3, "and", char_like(and_sign));
   id(5, "array", array_like);
   id(5, "begin", begin_like);
   id(4, "case", case_like);
   id(5, "const", const_like);
   id(3, "div", div_like);
   id(2, "do", do_like);
   id(6, "downto", to_like);
   id(4, "else", else_like);
   id(3, "end", end_like);
   id(4, "file", array_like);
   id(3, "for", for_like);
   id(8, "function", proc_like);
   id(4, "goto", goto_like);
   id(2, "if", if_like);
   id(2, "in", char_like(set_element_sign));
   id(5, "label", const_like);
   id(3, "mod", div_like);
   id(3, "nil", nil_like);
   id(3, "not", char_like(not_sign));
   id(2, "of", do_like);
   id(2, "or", char_like(or_sign));
   id(6, "packed", goto_like);
   id(9, "procedure", proc_like);
   id(7, "program", proc_like);
   id(6, "record", record_like);
   id(6, "repeat", repeat_like);
   id(3, "set", array_like);
   id(4, "then", do_like);
   id(2, "to", to_like);
   id(4, "type", const_like);
   id(5, "until", until_like);
   id(3, "var", var_like);
   id(5, "while", for_like);
   id(4, "with", for_like);
   id(7, "xclause", loop_like);
// 7.2???
   Phase_I(); Phase_II();
// ???19.1: Phase III: Output the cross-reference index
// We are nearly finished! ???WEAVE???'s only remaining task is to write out the index, after sorting the identifiers and index entries.
   phase_three ??? true, print("\nWriting the index...");
   if (change_exists) {
      finish_line();
   // ???19.3: Tell about changed modules
   // remember that the index is already marked as changed
      k_module ??? 1;
      outS("\\ch ");
      for (; k_module < module_count; k_module???) if (changed_module[k_module]) out_mod(k_module), outS(", ");
      out_mod(k_module), out1('.');
   // 19.3???
   }
   finish_line(), outS("\\inx"), finish_line();
// ???19.5: Do the first pass of sorting
// To begin the sorting, we go through all the hash lists and put each entry having a nonempty cross-reference list into the proper bucket.
   for (c ??? 0 ??? 0xff) bucket[c] ??? 0;
   for (h ??? hash_size) {
      next_name ??? hash[h];
      while (next_name ??? 0) {
         cur_name ??? next_name, next_name ??? link[cur_name];
         if (xref[cur_name] ??? 0) {
            c ??? byte_mem[cur_name%ww][byte_start[cur_name]];
            if (c ??? 'Z' && c ??? 'A') c += 0x20;
            blink[cur_name] ??? bucket[c], bucket[c] ??? cur_name;
         }
      }
   }
// 19.5???19.12: Sort and output the index
   sort_ptr ??? 0, unbucket(1);
   while (sort_ptr > 0) {
      cur_depth ??? cat[sort_ptr];
      if (blink[head[sort_ptr]] ??? 0 || cur_depth ??? infinity) {
      // ???19.14: Output index entries for the list at sort_ptr
         cur_name ??? head[sort_ptr];
      #if DEBUG
         if (trouble_shooting) debug_help();
      #endif // DEBUG
         do {
            outS("\\:");
         // ???19.15: Output the name at cur_name
            switch (ilk[cur_name]) {
               case normal: outS("\\%c", length(cur_name) ??? 1? '|': '\\'); break;
               case roman: break;
               case wildcard: outS("\\9"); break;
               case typewriter: outS("\\."); break;
               default: outS("\\&"); break;
            }
            out_name(cur_name)
         // 19.15???19.16: Output the cross-references at cur_name
         // Section numbers that are to be underlined are enclosed in ??????[??? ??? ???]??????.
         // ???19.17: Invert the cross-reference list at cur_name, making cur_xref the head
         // List inversion is best thought of as popping elements off one stack and pushing them onto another.
         // In this switch (cur_xref will be the head) begin the stack that we push things onto.
            this_xref ??? xref[cur_name], cur_xref ??? 0;
            do
               next_xref ??? xlink(this_xref), xlink(this_xref) ??? cur_xref,
               cur_xref ??? this_xref, this_xref ??? next_xref;
            while (this_xref ??? 0);
         // 19.17???
            do {
               outS(", "), cur_val ??? num(cur_xref);
               if (cur_val < def_flag) out_mod(cur_val);
               else outS("\\["), out_mod(cur_val - def_flag), out1(']');
               cur_xref ??? xlink(cur_xref);
            } while (cur_xref ??? 0);
            out1('.'), finish_line()
         // 19.16???
            cur_name ??? blink[cur_name];
         } while (cur_name ??? 0);
         sort_ptr???;
      // 19.14???
      } else {
      // ???19.13: Split the list at sort_ptr into further lists
         next_name ??? head[sort_ptr];
         do {
            cur_name ??? next_name, next_name ??? blink[cur_name];
            cur_byte ??? byte_start[cur_name] + cur_depth, cur_bank ??? cur_name%ww;
            if (cur_byte ??? byte_start[cur_name + ww]) c ??? 0;	// we hit the end of the name
            else {
               c ??? byte_mem[cur_bank][cur_byte];
               if (c ??? 'Z' && c ??? 'A') c += 0x20;
            }
            blink[cur_name] ??? bucket[c], bucket[c] ??? cur_name;
         } while (next_name ??? 0);
         sort_ptr???, unbucket(cur_depth + 1);
      // 19.13???
      }
   }
// 19.12???
   outS("\\fin"), finish_line();
// ???19.19: Output all the module names
   mod_print(root)
// 19.19???
   outS("\\con"), finish_line();
   print("Done.");
// 19.1???9.16: Check that all changes have been read
// At the end of the program, we will tell the user if the change file had a line that didn't match any relevant line in web_file.
   if (change_limit ??? 0) {	// changing is false
      for (ii ??? 0 ??? change_limit) buffer[ii] ??? change_buffer[ii];
      limit ??? change_limit, changing ??? true, line ??? other_line, loc ??? change_limit;
      err_print("! Change file entry did not match");
   }
// 9.16???
end_of_WEAVE:
#if STATS
// ???21.2: Print statistics about memory usage
   print("\nMemory usage statistics: %1d names, %1d cross references, %1d", name_ptr, xref_ptr, byte_ptr[0]);
   for (cur_bank ??? 1 ??? ww-1) print("+%1d", byte_ptr[cur_bank]);
   print(" bytes;");
   print("\nparsing required %1d scraps, %1d texts, %1d tokens, %1d levels;", max_scr_ptr, max_txt_ptr, max_tok_ptr, max_stack_ptr);
   print("\nsorting required %1d levels.", max_sort_ptr);
// 21.2???
#endif // STATS
// here files should be closed if the operating system requires it
// ???21.3: Print the job history
// Some implementations may wish to pass the history value to the operating system
// so that it can be used to govern whether or not other programs are started.
// Here we simply report the history to the user.
// (#) system dependencies
   switch (history) {
      case spotless: print("\n(No errors were found.)"); break;
      case harmless_message: print("\n(Did you see the warning message above?)"); break;
      case error_message: print("\n(Pardon me, but I think I spotted something wrong.)"); break;
      case fatal_message: print("\n(That was a fatal error, my friend.)"); break;
   }	// there are no other cases
// 21.3???
}
// 21.1???

// ??22. System-Dependent Changes.
// ???22.1:
// This module should be replaced, if necessary, by changes to the program that are necessary to make ???WEAVE??? work at a particular installation.
// It is usually best to design your change file so that all changes to previous modules preserve the module numbering;
// then everybody's version will be consistent with the printed program.
// More extensive changes, which introduce new modules, can be inserted here; then only the index itself will get a new module number.
// (#) system dependencies
// 22.1???

// ??23. Index.
// ???23.1:
// If you have read and understood the code for Phase III above, you know what is in this index and how it got here.
// All modules in which an identifier is used are listed with that identifier, except that reserved words are indexed
// only when they appear in format definitions, and the appearances of identifiers in module names are not indexed.
// Underlined entries correspond to where the identifier was declared.
// Error messages, control sequences put into the output, and a few other things like ???recursion??? are indexed here too.
// 23.1???
