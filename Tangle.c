// This program by D. E. Knuth is not copyrighted and can be used freely.
// Version 0 was released in December, 1981.
// Version 1 was released in September, 1982, with version 0 of TeX.
// Slight changes were made in October, 1982, for version 0.6 of TeX.
// Version 1.2 introduced {:nnn} comments, added @= and @\ (December, 1982).
// Version 1.4 added "history" (February, 1983).
// Version 1.5 conformed to TeX version 0.96 and fixed @\ (March, 1983).
// Version 1.7 introduced the new change file format (June, 1983).
// Version 2.0 was released in July, 1983, with version 0.999 of TeX.
// Version 2.5 was released in November, 1983, with version 1.0 of TeX.
// Version 2.6 fixed a bug: force-line-break after a constant (August, 1984).
// Version 2.7 fixed the definition of check_sum_prime (May, 1985).
// Version 2.8 fixed a bug in change_buffer movement (August, 1985).
// Version 2.9 allows nonnumeric macros before their def (December, 1988).
// Version 3, for Sewell's book, fixed long-line bug in input_ln (March, 1989).
// Version 4 was major change to allow 8-bit input (September, 1989).
// Version 4.1 conforms to ANSI standard for-loop rules (September, 1990).
// Version 4.2 fixes stat report if phase one dies (March, 1991).
// Version 4.3 fixes @ bug in verbatim, catches extra } (September, 1991).
// Version 4.4 activates debug_help on errors as advertised (February, 1993).
// Version 4.5 prevents modno-comments from being split across lines (Dec 2002).

// §1. Introduction.
// ‡1.1:
// This program converts a ‹WEB› file to a «Pas» file.
// It was written by D. E. Knuth in September, 1981; a somewhat similar ≪SAIL≫ program had been developed in March, 1979.
// Since this program describes itself, a bootstrapping process involving hand-translation had to be used to get started.

// For large ‹WEB› files one should have a large memory, since ‹TANGLE› keeps all the «Pas» text in memory (in an abbreviated form).
// The program uses a few features of the local «Pas» compiler that may need to be changed in other installations:
// 1)	Case statements have a default.
// 2)	Input-output routines may need to be adapted for use with a particular character set and/or for printing messages on the user's terminal.
// These features are also present in the «Pas» version of «TeX», where they are used in a similar (but more complex) way.
// System-dependent portions of ‹TANGLE› can be identified by looking at the entries for ‛system dependencies’ in the index below.
// (#) system dependencies

// The ‟banner line” defined here should be changed whenever ‹TANGLE› is modified.
#define banner "This is TANGLE, Version 4.5"
// 1.1‡1.2:
// The program begins with a fairly normal header, made up of pieces that will mostly be filled in later.
// (#) system dependencies
// The ‹WEB› input comes from files ≪web_file≫ and ≪change_file≫,
// the «Pas» output goes to file ≪Pascal_file≫, and the string pool output goes to file ≪pool≫.

// If it is necessary to abort the job because of a fatal error, the program calls the ‛≪jump_out()≫’ procedure, which goes to the label ≪end_of_TANGLE≫.

// ‡1.4: Compiler directives
// The «Pas» compiler used to develop this system has ‟compiler directives” that can appear in comments whose first character is a dollar sign.
// In production versions of ‹TANGLE› these directives tell the compiler that it is safe to avoid range checks
// and to leave out the extra code it inserts for the «Pas» debugger's benefit,
// although interrupts will occur if there is arithmetic overflow.
// (#) system dependencies
#pragma $C-,A+,D-	// no range check, catch arithmetic overflow, no debug overhead
#if DEBUG
#   pragma $C+,D+	// but turn everything on when debugging
#endif // DEBUG
// 1.4‡

// program TANGLE(web_file, change_file, Pascal_file, pool);
// ‡1.8: Constants in the outer block
// The following parameters are set big enough to handle «TeX», so they should be sufficient for most applications of ‹TANGLE›.
const int buf_size = 100;	// maximum length of input line
const int max_bytes = 45000;	// ≪1/ww≫ times the number of bytes in identifiers, strings, and module names; must be less than 0x10000
const int max_toks = 50000;	// ≪1/zz≫ times the number of bytes in compressed «Pas» code; must be less than 0x10000
const int max_names = 4000;	// number of identifiers, strings, module names; must be less than 0x2800
const int max_texts = 2000;	// number of replacement texts, must be less than 0x2800
const int hash_size = 353;	// should be prime
const int longest_name = 400;	// module names shouldn't be longer than this
const int line_length = 72;	// lines of «Pas» output have at most this many characters
const int out_buf_size = 144;	// length of output buffer, should be twice ≪line_length≫
const int stack_size = 50;	// number of simultaneous levels of macro expansion
const int max_id_length = 12;	// long identifiers are chopped to this length, which must not exceed ≪line_length≫
const int unambig_length = 7;	// identifiers must be unique if chopped to this length
				// note that 7 is more strict than «Pas»'s 8, but this can be varied
// 1.8‡
// 1.2‡

// ‡1.3:
// Some of this code is optional for use when debugging only; such material is conditioned on ≪DEBUG≫.
// Other parts, conditioned on ≪STATS≫, are optionally included if statistics about ‹TANGLE›'s memory usage are desired.
#define DEBUG false	// change this to ‛DEBUG ≡ true’ when debugging
#define STATS false	// change this to ‛STATS ≡ true’ when gathering usage statistics

// 1.3‡1.5:
// Editor's Notes:
// Generic labels are used for:
// ∙	‛reswitch:’	for the top of a «·switch·» statement that is being used as a finite-state control
// ∙	‛done:’		for a «·break·» two or more levels up
// ∙	‛not_found’	for a «·break·» from a search loop where the search came up empty

// 1.5‡1.6:
// Here are some macros for common programming idioms.
// Editor's Note:
// ∙	++, -- and {} ("do-nothing") are not needed when doing this in C.

// 1.6‡1.7:
// We assume that ≪case≫ statements may include a default case that applies if no matching label is found.
// Editor's Note:
// ∙	This is all subsumed by the syntax for switch statements in C.

// 1.7‡1.9: Globals in the outer block (1/28)
// A global variable called ≪history≫ will contain one of four values at the end of every run:
// ∙	≪spotless≫ means that no unusual messages were printed;
// ∙	≪harmless_message≫ means that a message of possible interest was printed but no serious errors were detected;
// ∙	≪error_message≫ means that at least one error was found;
// ∙	≪fatal_message≫ means that the program terminated abnormally.
// The value of ≪history≫ does not influence the behavior of the program;
// it is simply computed for the convenience of systems that might want to use such information.
inline void mark_harmless(void) {if (history ≡ spotless) history ← harmless_message; }
inline void mark_error(void) { history ← error_message; }
inline void mark_fatal(void) { history ← fatal_message; }

// ‡1.10: Set initial values (1/14)
enum {
   spotless = 0,		// ≪history≫ value for normal jobs
   harmless_message = 1,	// ≪history≫ value when non-serious info was printed
   error_message = 2,		// ≪history≫ value when an error was noted
   fatal_message = 3		// ≪history≫ value when we had to stop prematurely
} history ← spotless;	// how bad was this run?
// 1.10‡
// 1.9‡

// §2. The Character Set.
// ‡2.1: Types in the outer block (1/6)
// One of the main goals in the design of ‹WEB› has been to make it readily portable between a wide variety of computers.
// Yet ‹WEB› by its very nature must use a greater variety of characters than most computer programs deal with,
// and character encoding is one of the areas in which existing machines differ most widely from each other.

// To resolve this problem, all input to ‹WEAVE› and ‹TANGLE›
// is converted to an internal eight-bit code that is essentially standard ASCII, the ‟American Standard Code for Information Interchange.”
// The conversion is done immediately when each character is read in.
// Conversely, characters are converted from ASCII to the user's external representation just before they are output.
// (The original ASCII code was seven bits only; ‹WEB› now allows eight bits in an attempt to keep up with modern times.)

// Such an internal code is relevant to users of ‹WEB› only because it is the code used for preprocessed constants like ‹"A"›.
// If you are writing a program in ‹WEB› that makes use of such one-character constants,
// you should convert your input to ASCII form, like ‹WEAVE› and ‹TANGLE› do.
// Otherwise ‹WEB›'s internal coding scheme does not affect you.

// Here is a table of the standard visible ASCII codes:
//	xy │ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xa xb xc xd xe xf
//	───┼────────────────────────────────────────────────
//	2y │     !  "  #  $  %  &  '  (  )  *  +  ,  -  .  /
//	3y │  0  1  2  3  4  5  6  7  8  9  :  ;  <  =  >  ?
//	4y │  @  A  B  C  D  E  F  G  H  I  J  K  L  M  N  O
//	5y │  P  Q  R  S  T  U  V  W  X  Y  Z  [  \  ]  ^  _
//	6y │  `  a  b  c  d  e  f  g  h  i  j  k  l  m  n  o
//	7y │  p  q  r  s  t  u  v  w  x  y  z  {  |  }  ~
// (Actually, of course, code 0x20 is an invisible blank space.)
// Code 0x5e was once an upward arrow (‹‹char›0x0b›),
// and code 0x5f was once a left arrow (‹→›), in olden times when the first draft of ASCII code was prepared;
// but ‹WEB› works with today's standard ASCII in which those codes represent circumflex and underline as shown.
typedef enum {0x100} ASCII_code;	// eight-bit numbers, a subrange of the integers

// 2.1‡2.2: Types in the outer block (2/6)
// The original «Pas» compiler was designed in the late 60s, when six-bit character sets were common, so it did not make provision for lowercase letters.
// Nowadays, of course, we need to deal with both capital and small letters in a convenient way,
// so ‹WEB› assumes that it is being used with a «Pas» whose character set contains at least the characters of standard ASCII as listed above.
// Some «Pas» compilers use the original name ≪char≫ for the data type associated with the characters in text files,
// while other «Pas» s consider ≪char≫ to be a 64-element subrange of a larger data type that has some other name.

// In order to accommodate this difference, we shall use the name ≪text_char≫ to stand for the data type of the characters in the input and output files.
// We shall also assume that ≪text_char≫ consists of the elements ≪chr(first_text_char)≫ through ≪chr(last_text_char)≫, inclusive.
// The following definitions should be adjusted if necessary.
// (#) system dependencies
typedef char text_char char;	// the data type of characters in text files
#define first_text_char	0x00	// ordinal number of the smallest element of ≪text_char≫
#define last_text_char	0xff	// ordinal number of the largest element of ≪text_char≫

typedef packed file(text_char) text_file;

// 2.2‡2.3:: Globals in the outer block (2/28)
// The ‹WEAVE› and ‹TANGLE› processors convert between ASCII code and the user's external character set
// by means of arrays ≪xord≫ and ≪xchr≫ that are analogous to «Pas»'s ≪ord≫ and ≪chr≫ functions.
ASCII_code xord[text_char];	// specifies conversion of input characters
text_char xchr[ASCII_code] = {	// specifies conversion of output characters
// ‡2.7: Set initial values (3/14)
// ‡2.6: Local variables for initialization (1/4)
// When we initialize the ≪xord≫ array and the remaining parts of ≪xchr≫, it will be convenient to make use of an index variable, ≪i≫.
// Editor's Note
// ∙	Localized to the for loops where it is used; the loops in turn were eliminated.
// 2.6‡
// Here now is the system-dependent part of the character set.
// If ‹WEB› is being implemented on a garden-variety «Pas» for which only standard ASCII codes will appear in the input and output files,
// you don't need to make any changes here.
// But if you have, for example, an extended character set like the one in Appendix~C of ≪_ The «TeX» book _≫,
// the first line of code in this module should be changed to
//	≪for (enum {0x100} i ← 0x01 ⋯ 0x1f) xchr[i] ← chr(i);≫
// ‹WEB›'s character set is essentially identical to «TeX»'s, even with respect to characters less than 0x20.
// (#) system dependencies

// Changes to the present module will make ‹WEB› more friendly on computers that have an extended character set,
// so that one can type things like ‹≠› instead of ‹<>›.
// If you have an extended set of characters that are easily incorporated into text files,
// you can assign codes arbitrarily here, giving an ≪xchr≫ equivalent to whatever characters the users of ‹WEB› are allowed to have in their input files,
// provided that unsuitable characters do not correspond to special codes like ≪carriage_return≫ that are listed above.

// (The present file ‹TANGLE.WEB› does not contain any of the non-ASCII characters,
// because it is intended to be used with all implementations of ‹WEB›.
// It was originally created on a Stanford system that has a convenient extended character set,
// then ‟sanitized” by applying another program that transliterated all of the non-standard characters into standard equivalents.)

   "        "  "        "	// 00-07, 08-0f
   "        "  "        "	// 10-17, 18-1f

// ‡2.4: Set initial values (2/14)
// If we assume that every system using ‹WEB› is able to read and write the visible characters of standard ASCII
// (although not necessarily using the ASCII codes to represent them),
// the following assignment statements initialize most of the ≪xchr≫ array properly, without needing any system-dependent changes.
// For example, the statement ‹xchr[@'101] ← 'A'› that appears in the present ‹WEB› file
// might be encoded in, say, ≪EBCDIC≫ code on the external medium on which it resides,
// but ‹TANGLE› will convert from this external code to ASCII and back again.
// Therefore the assignment statement ‹XCHR[65] ← 'A'› will appear in the corresponding «Pas» file,
// and «Pas» will compile this statement so that ≪xchr[65]≫ receives the character ‹A› in the external (≪char≫) code.
// Note that it would be quite incorrect to say ‹xchr[@'101] ← "A"›,
// because ≪"A"≫ is a constant of type ≪integer≫, not ≪char≫, and because we have ≪"A"≫ = 65 regardless of the external character set.
   " !\"#$%&'" "()*+,-./"	// 20-27, 28-2f
   "01234567"  "89:;<=>?"	// 30-37, 38-3f
   "@ABCDEFG"  "HIJKLMNO"	// 40-47, 48-4f
   "PQRSTUVW"  "XYZ[\\]^_"	// 50-57, 58-5f
   "`abcdefg"  "hijklmno"	// 60-67, 68-6f
   "pqrstuvw"  "xyz{|}~ "	// 70-77, 78-7f // The ASCII codes 0x00 (above) and 0x7f are not used.
// 2.4‡

   "        "  "        "	// 80-87, 88-8f
   "        "  "        "	// 90-97, 98-9f
   "        "  "        "	// a0-a7, a8-af
   "        "  "        "	// b0-b7, b8-bf
   "        "  "        "	// c0-c7, c8-cf
   "        "  "        "	// d0-d7, d8-df
   "        "  "        "	// e0-e7, e8-ef
   "        "  "        "	// f0-f7, f8-ff
// 2.7‡
};
// 2.3‡2.5:
// Some of the ASCII codes below 0x20 have been given symbolic names in ‹WEAVE› and ‹TANGLE› because they are used with a special meaning.
#define and_sign		0x04	// equivalent to ‛‹and›’
#define not_sign		0x05	// equivalent to ‛‹not›’
#define set_element_sign	00x6	// equivalent to ‛‹in›’
#define tab_mark		0x09	// ASCII code used as tab-skip
#define line_feed		0x0a	// ASCII code thrown away at end of line
#define form_feed		0x0c	// ASCII code used at end of page
#define carriage_return		0x0d	// ASCII code used at end of line
#define left_arrow		0x18	// equivalent to ‛‹:=›’
#define not_equal		0x1a	// equivalent to ‛‹<>›’
#define less_or_equal		0x1c	// equivalent to ‛‹<=›’
#define greater_or_equal	0x1d	// equivalent to ‛‹>=›’
#define equivalence_sign	0x1e	// equivalent to ‛‹==›’
#define or_sign			0x1f	// equivalent to ‛‹or›’
// 2.5‡

// §3. Input and Output.
// ‡3.1:
// The input conventions of this program are intended to be very much like those of «TeX»
// (except, of course, that they are much simpler, because much less needs to be done).
// Furthermore they are identical to those of ‹WEAVE›.
// Therefore people who need to make modifications to all three systems should be able to do so without too many headaches.

// We use the standard «Pas» input/output procedures in several places that «TeX» cannot,
// since ‹TANGLE› does not have to deal with files that are named dynamically by the user, and since there is no input from the terminal.

// 3.1‡3.2: Globals in the outer block (3/28)
// Terminal output is done by writing on file ≪term_out≫, which is assumed to consist of characters of type ≪text_char≫:
// (#) system dependencies

// Editor's Note:
// ∙	The original print_ln(A, ...), new_line() and print_nl(A, ...)
//	are subsumed respectively by print(A "\n", ...), print("\n") and print("\n" A, ...)
// ∙	The original rewrite(A, ...) is subsumed by fopen()
// ∙	The original update_terminal(A, ...) is subsumed by fflush()
inline void print(char *A, ...) { fprintf(term_out, A, ...); }	// ‛≪print≫’ means write on the terminal
inline void write(text_file F, char *A, ...) { fprintf(F, A, ...); }
#define rewrite(F) (F = fopen(F##_name, "wa"))

text_file term_out;	// the terminal as an output file

// 3.2‡3.4:
// The ≪update_terminal()≫ procedure is called when we want
// to make sure that everything we have output to the terminal so far has actually left the computer's internal buffers and been sent.
// (#) system dependencies
inline void update_terminal(void) { fflush(term_out); }	// empty the terminal output buffer

// 3.4‡3.5: Globals in the outer block (4/28)
// The main input comes from ≪web_file≫; this input may be overridden by changes in ≪change_file≫.
// (If ≪change_file≫ is empty, there are no changes.)
text_file web_file;	// primary input
text_file change_file;	// updates

// 3.5‡3.6:
// The following code opens the input files. Since these files were listed in the program header,
// we assume that the «Pas» runtime system has already checked that suitable file names have been given;
// therefore no additional error checking needs to be done.
// (#) system dependencies
void open_input(void) {	// prepare to read ≪web_file≫ and ≪change_file≫
   reset(web_file), reset(change_file);
}

// 3.6‡3.7: Globals in the outer block (5/28)
// The main output goes to ≪Pascal_file≫, and string pool constants are written to the ≪pool≫ file.
text_file Pascal_file;
text_file pool;

// 3.7‡3.9: Globals in the outer block (6/28)
// Input goes into an array called ≪buffer≫.
ASCII_code buffer[0..buf_size];

// 3.9‡3.10:
// The ≪input_ln()≫ procedure brings the next line of input from the specified file into the ≪buffer≫ array and returns the value ≪true≫,
// unless the file has already been entirely read, in which case it returns ≪false≫.
// The conventions of «TeX» are followed; i.e., ≪ASCII_code≫ numbers representing the next line of the file
// are input into ≪buffer[0]≫, ≪buffer[1]≫, ‹dots›, ≪buffer[limit - 1]≫;
// trailing blanks are ignored; and the global variable ≪limit≫ is set to the length of the line.
// (#) system dependencies
// The value of ≪limit≫ must be strictly less than ≪buf_size≫.

// We assume that none of the ≪ASCII_code≫ values of ≪buffer[j]≫ for ≪0 ≤ j < limit≫ is equal to 0, 0x7f, ≪line_feed≫, ≪form_feed≫, or ≪carriage_return≫.
boolean input_ln(text_file &f) {	// inputs a line or returns ≪false≫
   enum {0..buf_size} final_limit ← limit ← 0;	// ≪limit≫ without trailing blanks
   if (eof(f)) return false;
   while (!eoln(f)) {
      buffer[limit↑] ← xord[f^], get(f);
      if (buffer[limit - 1] ≠ ' ') final_limit ← limit;
      if (limit ≡ buf_size) {
         while (!eoln(f)) get(f);
         limit↓;	// keep ≪buffer[buf_size]≫ empty
         if (final_limit > limit) final_limit ← limit;
         print("\n! Input line too long"), loc ← 0, error();
      }
   }
   read_ln(f), limit ← final_limit;
   return true;
}
// 3.10‡

// §4. Reporting Errors to the User.
// ‡1.2: [continued]
// ‡4.1: Globals in the outer block (7/28)
// The ‹TANGLE› processor operates in two phases: first it inputs the source file and stores a compressed representation of the program,
// then it produces the «Pas» output from the compressed representation.

// The global variable ≪phase_one≫ tells whether we are in Phase I or not.
boolean phase_one;	// ≪true≫ in Phase I, ≪false≫ in Phase II
// 4.1‡4.2: Error handling procedures (1/3)
// If an error is detected while we are debugging, we usually want to look at the contents of memory.
// A special procedure will be declared later for this purpose.
#if DEBUG
void debug_help(void);
#endif // DEBUG

// 4.2‡4.3: Error handling procedures (2/3)
// During the first phase, syntax errors are reported to the user by saying
//	‛≪err_print("! Error message")≫’,
// followed by ‛≪jump_out()≫’ if no recovery from the error is provided.
// This will print the error message followed by an indication of where the error was spotted in the source file.
// Note that no period follows the error message, since the error routine will automatically supply a period.

// Errors that are noticed during the second phase are reported to the user in the same fashion,
// but the error message will be followed by an indication of where the error was spotted in the output file.

// The actual error indications are provided by a procedure called ≪error()≫.
inline void err_print(A, ...) { print("\n" A, ...), error(); }

void error(void) {	// prints "‹.›" and location of error message
   if (phase_one) {
   // ‡4.4: Print error location based on input buffer
   // The error locations during Phase I can be indicated by using the global variables ≪loc≫, ≪line≫, and ≪changing≫,
   // which tell respectively the first unlooked-at position in ≪buffer≫, the current line number,
   // and whether or not the current line is from ≪change_file≫ or ≪web_file≫.
   // This routine should be modified on systems whose standard text editor has special line-numbering conventions.
   // (#) system dependencies
      if (changing) print(". (change file "); else print(". (");
      print("l.%1d)\n", line);
      enum {0..buf_size} l ← loc ≥ limit? limit: loc;	// index into ≪buffer[]≫
      for (enum {0..buf_size} k ∈ l) print("%c", buffer[k] ≡ tab_mark? ' ': xchr[buffer[k]]);	// print the characters already read
      print("\n");
      for (enum {0..buf_size} k ∈ l) print(" ");	// space out the next line
      for (enum {0..buf_size} k ← l ⋯ limit - 1) print("%c", xchr[buffer[k]]);	// print the part not yet read
      print(" ");	// this space separates the message from future asterisks
   // 4.4‡
   } else {
   // ‡4.5: Print error location based on output buffer
   // The position of errors detected during the second phase can be indicated by outputting the partially-filled output buffer,
   // which contains ≪out_ptr≫ entries.
   print(". (l.%1d)\n", line);
   for (enum 0..out_buf_size} j ← 1 ⋯ out_ptr) print(xchr[out_buf[j - 1]]);	// print current partial line
   print("... ");	// indicate that this information is partial
// 4.5‡
   }
   update_terminal(), mark_error();
#if DEBUG
   debug_skipped ← debug_cycle, debug_help();
#endif // DEBUG
}

// 4.3‡4.6: Error handling procedures (3/3)
// The ≪jump_out()≫ procedure just cuts across all active procedure levels and jumps out of the program.
// This is the only non-local ≪goto≫ statement in ‹TANGLE›.
// It is used when no recovery from a particular error has been provided.

// Some «Pas» compilers do not implement non-local ≪goto≫ statements.
// (#) system dependencies
// In such cases the code that appears at label ≪end_of_TANGLE≫ should be copied into the ≪jump_out()≫ procedure,
// followed by a call to a system procedure that terminates the program.
inline void fatal_error(A, ...) { print("\n" A, ...), error(), mark_fatal(), jump_out(); }

void jump_out(void) {
   goto end_of_TANGLE;
}
// 4.6‡
// 1.2‡

// ‡4.7:
// Sometimes the program's behavior is far different from what it should be,
// and ‹TANGLE› prints an error message that is really for the ‹TANGLE› maintenance person, not the user.
// In such cases the program says ≪confusion("indication of where we are")≫.
#define confusion(A) (fatal_error("! This can't happen (" A ")"))

// 4.7‡4.8:
// An overflow stop occurs if ‹TANGLE›'s tables aren't large enough.
#define overflow(A) (fatal_error("! Sorry, " A " capacity exceeded"))
// 4.8‡

// §5. Data Structures.
// ‡5.1: Types in the outer block (3/6)
// Most of the user's «Pas» code is packed into eight-bit integers in two large arrays called ≪byte_mem[]≫ and ≪tok_mem[]≫.
// The ≪byte_mem[]≫ array holds the names of identifiers, strings, and modules;
// the ≪tok_mem[]≫ array holds the replacement texts for macros and modules.
// Allocation is sequential, since things are deleted only during Phase II, and only in a last-in-first-out manner.

// Auxiliary arrays ≪byte_start≫ and ≪tok_start≫ are used as directories to ≪byte_mem[]≫ and ≪tok_mem[]≫,
// and the ≪link≫, ≪ilk≫, ≪equiv≫, and ≪text_link≫ arrays give further information about names.
// These auxiliary arrays consist of sixteen-bit items.
typedef enum {0x100} eight_bits;	// unsigned one-byte quantity
typedef enum {0x10000} sixteen_bits;	// unsigned two-byte quantity

// 5.1‡5.2: Globals in the outer block (8/28)
// ‹TANGLE› has been designed to avoid the need for indices that are more than sixteen bits wide, so that it can be used on most computers.
// But there are programs that need more than 0x10000 tokens, and some programs even need more than 0x10000 bytes; «TeX» is one of these.
// To get around this problem, a slight complication has been added to the data structures:
// ≪byte_mem[]≫ and ≪tok_mem[]≫ are two-dimensional arrays, whose first index is either 0 or 1.
// (For generality, the first index is actually allowed to run between 0 and ≪ww - 1≫ in ≪byte_mem[]≫,
// or between 0 and ≪zz - 1≫ in ≪tok_mem[]≫, where ≪ww≫ and ≪zz≫ are set to 2 and~3;
// the program will work for any positive values of ≪ww≫ and ≪zz≫, and it can be simplified in obvious ways if ≪ww ≡ 1≫ or ≪zz ≡ 1≫.)
#define ww 2	// we multiply the byte capacity by approximately this amount
#define zz 3	// we multiply the token capacity by approximately this amount

ASCII_code packed byte_mem[ww][0..max_bytes];	// characters of names
eight_bits packed tok_mem[zz][0..max_toks];	// tokens
// ‡5.6: Set initial values (7/14)
// ‡5.5: Local variables for initialization (2/4)
// Editor's Note
// ∙	Localized to the for loop where it is used; the loop in turn was eliminated.
// 5.5‡
sixteen_bits byte_start[0..max_names] ← {0, 0, 0};	// directory into ≪byte_mem[]≫
// byte_start[ww] ← 0;	// this makes name 0 of length zero
// 5.6‡5.10: Set initial values (8/14)
// ‡5.9: Local variables for initialization (3/4)
// Editor's Note
// ∙	Localized to the for loop where it is used; the loop in turn was eliminated.
sixteen_bits tok_start[0..max_texts] ← {0, 0, 0, 0};	// directory into ≪tok_mem[]≫
// 5.9‡
// tok_start[zz] ← 0;	// this makes replacement text 0 of length zero
// 5.10‡
sixteen_bits link[0..max_names];	// hash table or tree links
// ‡5.12: Set initial values (9/14)
sixteen_bits ilk[0..max_names] ← {0};	// type codes or tree links
// rlink[0] ← 0;	// the binary search tree starts out with nothing in it
sixteen_bits equiv[0..max_names] ← {0};	// info corresponding to names
// equiv[0] ← 0;	// the undefined module has no replacement text
// 5.12‡8.2: Set initial values (11/14)
sixteen_bits text_link[0..max_texts] ← 0;	// relates replacement texts
// 8.2‡

// 5.2‡5.3: Types in the outer block (4/6)
// The names of identifiers are found by computing a hash address ≪h≫
// and then looking at strings of bytes signified by ≪hash[h]≫, ≪link[hash[h]]≫, ≪link[link[hash[h]]]≫, ‹dots›,
// until either finding the desired name or encountering a zero.

// A ‛≪name_pointer≫’ variable, which signifies a name, is an index into ≪byte_start≫.
// The actual sequence of characters in the name pointed to by ≪p≫ appears in positions ≪byte_start[p]≫ to ≪byte_start[p + ww] - 1≫, inclusive,
// in the segment of ≪byte_mem[]≫ whose first index is ≪p%ww≫.
// Thus, when ≪ww ≡ 2≫ the even-numbered name bytes appear in ≪byte_mem[0][]≫ and the odd-numbered ones appear in ≪byte_mem[1][]≫.
// The pointer 0 is used for undefined module names; we don't want to use it for the names of identifiers,
// since 0 stands for a null pointer in a linked list.

// Strings are treated like identifiers; the first character (a double-quote) distinguishes a string from an alphabetic name,
// but for ‹TANGLE›'s purposes strings behave like numeric macros.
// (A ‛string’ here refers to the strings delimited by double-quotes that ‹TANGLE› processes.
// «Pas» string constants delimited by single-quote marks are not given such special treatment;
// they simply appear as sequences of characters in the «Pas» texts.)
// The total number of strings in the string pool is called ≪string_ptr≫, and the total number of names in ≪byte_mem[]≫ is called ≪name_ptr≫.
// The total number of bytes occupied in ≪byte_mem[w][]≫ is called ≪byte_ptr[w]≫.

// We usually have ≪byte_start[name_ptr + w] ≡ byte_ptr[(name_ptr + w)%ww]≫ for ≪0 ≤ w < ww≫,
// since these are the starting positions for the next ≪ww≫ names to be stored in ≪byte_mem[]≫.
#define length(A) (byte_start[A + ww] - byte_start[A])	// the length of a name

typedef enum {0..max_names} name_pointer;	// identifies a name

// 5.3‡5.4: Globals in the outer block (9/28)
// ‡5.6: Set initial values (7/14) [continued]
name_pointer name_ptr ← 1;			// first unused position in ≪byte_start≫
name_pointer string_ptr ← 0x100;		// next number to be given to a string of length ≪ ≠ 1≫
enum {0..max_bytes} byte_ptr[ww] ← {0, 0};	// first unused position in ≪byte_mem[]≫
integer pool_check_sum ← 271828;		// sort of a hash for the whole string pool
// 5.6‡

// 5.4‡5.7: Types in the outer block (5/6)
// Replacement texts are stored in ≪tok_mem[]≫, using similar conventions.
// A ‛≪text_pointer≫’ variable is an index into ≪tok_start≫,
// and the replacement text that corresponds to ≪p≫ runs from positions ≪tok_start[p]≫ to ≪tok_start[p + zz] - 1≫, inclusive,
// in the segment of ≪tok_mem[]≫ whose first index is ≪p%zz≫.
// Thus, when ≪zz ≡ 2≫ the even-numbered replacement texts appear in ≪tok_mem[0][]≫ and the odd-numbered ones appear in ≪tok_mem[1][]≫.
// Furthermore, ≪text_link[p]≫ is used to connect pieces of text that have the same name, as we shall see later.
// The pointer 0 is used for undefined replacement texts.

// The first position of ≪tok_mem[z][]≫ that is unoccupied by replacement text is called ≪tok_ptr[z]≫,
// and the first unused location of ≪tok_start≫ is called ≪text_ptr≫.
// We usually have the identity ≪tok_start[text_ptr + z] ≡ tok_ptr[(text_ptr + z)%zz]≫, for ≪0 ≤ z < zz≫,
// since these are the starting positions for the next ≪zz≫ replacement texts to be stored in ≪tok_mem[]≫.
typedef enum {0..max_texts} text_pointer;	// identifies a replacement text

// 5.7‡5.8: Globals in the outer block (10/28)
// It is convenient to maintain a variable ≪z≫ that is equal to ≪text_ptr%zz≫, so that we always insert tokens into segment ≪z≫ of ≪tok_mem[]≫.
// ‡5.10: Set initial values (8/14) [continued]
text_pointer text_ptr ← 1;	// first unused position in ≪tok_start≫
enum {0..max_toks} tok_ptr[zz] ← {0, 0, 0};	// first unused position in a given segment of ≪tok_mem[]≫
enum {zz} z ← 1%zz;	// current segment of ≪tok_mem[]≫
// 5.10‡
#if STATS
enum {0..max_toks} max_tok_ptr[zz];	// largest values assumed by ≪tok_ptr≫
#endif // STATS

// 5.8‡5.11:
// Four types of identifiers are distinguished by their ≪ilk≫:
// ∙	≪normal≫ identifiers will appear in the «Pas» program as ordinary identifiers since they have not been defined to be macros;
//	the corresponding value in the ≪equiv≫ array for such identifiers is a link in a secondary hash table
//	that is used to check whether any two of them agree in their first ≪unambig_length≫ characters
//	after underline symbols are removed and lowercase letters are changed to uppercase.
// ∙	≪numeric≫ identifiers have been defined to be numeric macros;
//	their ≪equiv≫ value contains the corresponding numeric value plus $2^{15}$.
//	Strings are treated as numeric macros.
// ∙	≪simple≫ identifiers have been defined to be simple macros; their ≪equiv≫ value points to the corresponding replacement text.
// ∙	≪parametric≫ identifiers have been defined to be parametric macros; like simple identifiers, their ≪equiv≫ value points to the replacement text.
#define normal 0	// ordinary identifiers have ≪normal≫ ilk
#define numeric 1	// numeric macros and strings have ≪numeric≫ ilk
#define simple 2	// simple macros have ≪simple≫ ilk
#define parametric 3	// parametric macros have ≪parametric≫ ilk

// 5.11‡5.12: Set initial values (9/14)
// The names of modules are stored in ≪byte_mem[]≫ together with the identifier names,
// but a hash table is not used for them because ‹TANGLE› needs to be able to recognize a module name when given a prefix of that name.
// A conventional binary seach tree is used to retrieve module names, with fields called ≪llink≫ and ≪rlink≫ in place of ≪link≫ and ≪ilk≫.
// The root of this tree is ≪rlink[0]≫. If ≪p≫ is a pointer to a module name, ≪equiv[p]≫ points to its replacement text,
// just as in simple and parametric macros, unless this replacement text has not yet been defined (in which case ≪equiv[p] ≡ 0≫).
#define llink link	// left link in binary search tree for module names
#define rlink ilk	// right link in binary search tree for module names

// rlink[0] ← 0;	// the binary search tree starts out with nothing in it
// equiv[0] ← 0;	// the undefined module has no replacement text

// 5.12‡5.13:
// Here is a little procedure that prints the text of a given name.
void print_id(name_pointer p) {	// print identifier or module name
   if (p ≥ name_ptr) print("IMPOSSIBLE");
   else {
      enum {ww} w ← p%ww;	// segment of ≪byte_mem[]≫
      for (enum {0..max_bytes} k ← byte_start[p] ⋯ byte_start[p + ww] - 1) print(xchr[byte_mem[w][k]]);
   }
}
// 5.13‡

// §6. Searching for Identifiers.
// ‡6.1: Globals in the outer block (11/28)
// The hash table described above is updated by the ≪id_lookup()≫ procedure,
// which finds a given identifier and returns a pointer to its index in ≪byte_start≫.
// If the identifier was not already present, it is inserted with a given ≪ilk≫ code;
// and an error message is printed if the identifier is being doubly defined.

// Because of the way ‹TANGLE›'s scanning mechanism works,
// it is most convenient to let ≪id_lookup()≫ search for an identifier that is present in the ≪buffer≫ array.
// Two other global variables specify its position in the buffer:
// the first character is ≪buffer[id_first]≫, and the last is ≪buffer[id_loc - 1]≫.
// Furthermore, if the identifier is really a string,
// the global variable ≪double_chars≫ tells how many of the characters in the buffer appear twice (namely ‹@@› and ‹""›),
// since this additional information makes it easy to calculate the true length of the string.
// The final double-quote of the string is not included in its ‟identifier”, but the first one is,
// so the string length is ≪id_loc-id_first-double_chars - 1≫.

// We have mentioned that ≪normal≫ identifiers belong to two hash tables, one for their true names as they appear in the ‹WEB› file
// and the other when they have been reduced to their first ≪unambig_length≫ characters.
// The hash tables are kept by the method of simple chaining, where the heads of the individual lists appear in the ≪hash≫ and ≪chop_hash≫ arrays.
// If ≪h≫ is a hash code, the primary hash table list starts at ≪hash[h]≫ and proceeds through ≪link≫ pointers;
// the secondary hash table list starts at ≪chop_hash[h]≫ and proceeds through ≪equiv≫ pointers.
// Of course, the same identifier will probably have two different values of ≪h≫.

// The ≪id_lookup()≫ procedure uses an auxiliary array called ≪chopped_id≫ to contain up to ≪unambig_length≫ characters of the current identifier,
// if it is necessary to compute the secondary hash code.
// (This array could be declared local to ≪id_lookup()≫, but in general we are making all array declarations global in this program,
// because some compilers and some machine architectures make dynamic array allocation inefficient.)
enum {0..buf_size} id_first;		// where the current identifier begins in the buffer
enum {0..buf_size} id_loc;		// just after the current identifier in the buffer
enum {0..buf_size} double_chars;	// correction to length in case of strings

// ‡6.3: Set initial values (10/14)
// ‡6.2: Local variables for initialization (4/4)
// Editor's Note
// ∙	Localized to the for loop where it is used; the loop in turn was eliminated.
// Initially all the hash lists are empty.
// for (enum {0..hash_size} h ∈ hash_size) hash[h] ← 0, chop_hash[h] ← 0;
sixteen_bits hash[0..hash_size], chop_hash[0..hash_size];	// heads of hash lists
// 6.2‡
// 6.3‡
ASCII_code chopped_id[0..unambig_length];	// chopped identifier

// 6.1‡6.4:
// Here now is the main procedure for finding identifiers (and strings).
// The parameter ≪t≫ is set to ≪normal≫ except when the identifier is a macro name that is just being defined;
// in the latter case, ≪t≫ will be ≪numeric≫, ≪simple≫, or ≪parametric≫.
name_pointer id_lookup(eight_bits t) {	// finds current identifier
   enum {0..buf_size} l ← id_loc - id_first;	// compute the length of the given identifier
// ‡6.5: Compute the hash code ≪h≫
// (#) Error: The original comment listed c₁ c₂ … c_m instead of c₁ c₂ c_n.
// A simple hash code is used: If the sequence of ASCII codes is $c₁ c₂ … c_n$, its hash value will be
//	(2ⁿ⁻¹ c₁ + 2ⁿ⁻² c₂ + ⋯ + c_n) \bmod ≪hash_size≫.
   enum {0..hash_size} h ← buffer[id_first];	// hash code
   for (enum {0..buf_size} i ← id_first + 1; i < id_loc; i↑) h ← (h + h + buffer[i])%hash_size;
// 6.5‡6.6: Compute the name location ≪p≫
// If the identifier is new, it will be placed in position ≪p ≡ name_ptr≫, otherwise ≪p≫ will point to its existing location.
   enum {name_pointer} p ← hash[h];	// where the identifier is being sought
   for (; p ≠ 0; p ← link[p]) if (length(p) ≡ l) {
   // ‡6.7: Compare name ≪p≫ with current identifier, ≪break;≫ if equal
      enum {0..buf_size} i ← id_first;	// index into ≪buffer≫
      enum {0..max_bytes} k ← byte_start[p];	// index into ≪byte_mem[]≫
      enum {ww} w ← p%ww;	// segment of ≪byte_mem[]≫
      for (; i < id_loc ∧ buffer[i] ≡ byte_mem[w][k]; i↑, k↑);
      if (i ≡ id_loc) break;	// all characters agree
   // 6.7‡
   }
   if (p ≡ 0) {
      p ← name_ptr;	// the current identifier is new
      link[p] ← hash[h], hash[h] ← p;	// insert ≪p≫ at beginning of hash list
   }
// 6.6‡
   if (p ≡ name_ptr ∨ t ≠ normal) {
   // ‡6.8: Update the tables and check for possible errors
      if (p ≠ name_ptr ∧ t ≠ normal ∧ ilk[p] ≡ normal ∨ p ≡ name_ptr ∧ t ≡ normal ∧ buffer[id_first] ≠ '"') {
      // ‡6.9: Compute the secondary hash code ≪h≫ and put the first characters into the auxiliary array ≪chopped_id≫
      // The following routine, which is called into play when it is necessary to look at the secondary hash table,
      // computes the same hash function as before (but on the chopped data),
      // and places a zero after the chopped identifier in ≪chopped_id≫ to serve as a convenient sentinel.
         enum {0..buf_size} i ← id_first;	// index into ≪buffer[]≫
         enum {0..unambig_length} s ← 0;	// index into ≪chopped_id≫
         h ← 0;
         for (; i < id_loc ∧ s < unambig_length; i↑) if (buffer[i] ≠ '_') {
            chopped_id[s] ← buffer[i] ≥ 'a'? buffer[i] - 0x20: buffer[i];
            h ← (h + h + chopped_id[s↑])%hash_size;
         }
         chopped_id[s] ← 0;
      // 6.9‡
      }
      if (p ≠ name_ptr) {
      // ‡6.10: Give double-definition error, if necessary, and change ≪p≫ to type ≪t≫
      // If a nonnumeric macro has appeared before it was defined, ‹TANGLE› will still work all right;
      // after all, such behavior is typical of the replacement texts for modules, which act very much like macros.
      // However, an undefined numeric macro may not be used on the right-hand side of another numeric macro definition,
      // so ‹TANGLE› finds it simplest to make a blanket rule that numeric macros should be defined before they are used.
      // The following routine gives an error message and also fixes up any damage that may have been caused.
      // now ≪p ≠ name_ptr≫ and ≪t ≠ normal≫
         if (ilk[p] ≡ normal) {
            if (t ≡ numeric) err_print("! This identifier has already appeared");
         // ‡6.11: Remove ≪p≫ from secondary hash table
         // When we have to remove a secondary hash entry, because a ≪normal≫ identifier is changing to another ≪ilk≫,
         // the hash code ≪h≫ and chopped identifier have already been computed.
            enum {name_pointer} q ← chop_hash[h];	// where the identifier is being sought
            if (q ≡ p) chop_hash[h] ← equiv[p];
            else {
               for (; equiv[q] ≠ p; q ← equiv[q]);
               equiv[q] ← equiv[p];
            }
         // 6.11‡
         } else err_print("! This identifier was defined before");
         ilk[p] ← t;
      // 6.10‡
      } else {
      // ‡6.12: Enter a new identifier into the table at position ≪p≫
      // The following routine could make good use of a generalized ≪pack≫ procedure
      // that puts items into just part of a packed array instead of the whole thing.
         if (t ≡ normal ∧ buffer[id_first] ≠ '"') {
         // ‡6.13: Check for ambiguity and update secondary hash
            for (enum {name_pointer} q ← chop_hash[h]; q ≠ 0; q ← equiv[q]) {
            // ‡6.14: Check if ≪q≫ conflicts with ≪p≫
               enum {0..max_bytes} k ← byte_start[q];	// index into ≪byte_mem[]≫
               enum {0..unambig_length} s ← 0;	// index into ≪chopped_id≫
               enum {ww} w ← q%ww;	// segment of ≪byte_mem[]≫
               for (; k < byte_start[q + ww] ∧ s < unambig_length; k↑)  {
                  eight_bits c ← byte_mem[w][k];	// byte being chopped
                  if (c ≠ '_') {
                     if (c ≥ 'a') c -= 0x20;	// merge lowercase with uppercase
                     if (chopped_id[s] ≠ c) goto not_found;
                     s↑;
                  }
               }
               if (k ≠ byte_start[q + ww] ∨ chopped_id[s] ≡ 0) {
                  print("\n! Identifier conflict with ");
                  for (k ← byte_start[q] ⋯ byte_start[q + ww] - 1) print(xchr[byte_mem[w][k]]);
                  error(), q ← 0;	// only one conflict will be printed, since ≪equiv[0] ≡ 0≫
               }
            not_found:
            // 6.14‡
            }
            equiv[p] ← chop_hash[h], chop_hash[h] ← p;	// put ≪p≫ at front of secondary list
         // 6.13‡
         }
         enum {ww} w ← name_ptr%ww;	// segment of ≪byte_mem[]≫
         enum {0..max_bytes} k ← byte_ptr[w];	// index into ≪byte_mem[]≫
         if (k + l > max_bytes) overflow("byte memory");
         if (name_ptr > max_names - ww) overflow("name");
         enum {0..buf_size} i ← id_first;	// get ready to move the identifier into ≪byte_mem[]≫
         while (i < id_loc) byte_mem[w][k↑] ← buffer[i↑];
         byte_start[name_ptr↑ + ww] ← byte_ptr[w] ← k;
         if (buffer[id_first] ≠ '"') ilk[p] ← t;
         else {
         // ‡6.15: Define and output a new string of the pool
         // We compute the string pool check sum by working modulo a prime number that is large but not so large that overflow might occur.
            const integer check_sum_prime = 0x1ffffb7;	// 2²⁹ - 73
            ilk[p] ← numeric;	// strings are like numeric macros
            if (l-double_chars ≡ 2)	// this string is for a single character
               equiv[p] ← buffer[id_first + 1] + 0x8000;
            else {
               equiv[p] ← string_ptr + 0x8000;
               l -= double_chars + 1;
               if (l > 99) err_print("! Preprocessed string is too long");
               string_ptr↑;
               write(pool, "%c%c", xchr['0' + l/10], xchr['0' + l%10]);	// output the length
               pool_check_sum += pool_check_sum + l;
               while (pool_check_sum > check_sum_prime) pool_check_sum -= check_sum_prime;
               for (enum {0..buf_size} i ← id_first + 1; i < id_loc; i↑) {
                  write(pool, "%c", xchr[buffer[i]]);	// output characters of string
                  pool_check_sum += pool_check_sum + buffer[i];
                  while (pool_check_sum > check_sum_prime) pool_check_sum -= check_sum_prime;
                  if (buffer[i] ≡ '"' ∨ buffer[i] ≡ '@') i↑;	// omit second appearance of doubled character
               }
               write(pool, "\n");
            }
         // 6.15‡
         }
      // 6.12‡
      }
   // 6.8‡
   }
   return p;
}
// 6.4‡

// §7. Searching for Module Names.
// ‡7.1: Globals in the outer block (12/28)
// The ≪mod_lookup()≫ procedure finds the module name ≪mod_text[1..l]≫ in the search tree,
// after inserting it if necessary, and returns a pointer to where it was found.
// ‡13.10: Set initial values (13/14)
// Module names are placed into the ≪mod_text≫ array with consecutive spaces, tabs, and carriage-returns replaced by single spaces.
// There will be no spaces at the beginning or the end.
// (We set ≪mod_text[0] ← ' '≫ to facilitate this, since the ≪mod_lookup()≫ routine uses ≪mod_text[1]≫ as the first character of the name.)
ASCII_code mod_text[0..longest_name] ← ' ';	// name being sought for
// 13.10‡

// 7.1‡7.2:
// According to the rules of ‹WEB›, no module name should be a proper prefix of another, so a ‟clean” comparison should occur between any two names.
// The result of ≪mod_lookup()≫ is 0 if this prefix condition is violated.
// An error message is printed when such violations are detected during phase two of ‹WEAVE›.
#define less		0	// the first name is lexicographically less than the second
#define equal		1	// the first name is equal to the second
#define greater		2	// the first name is lexicographically greater than the second
#define prefix		3	// the first name is a proper prefix of the second
#define extension	4	// the first name is a proper extension of the second

name_pointer mod_lookup(sixteen_bits l) {	// finds module name
   enum {less..extension} c ← greater;	// comparison between two names
   name_pointer q ← 0;	// father of node ≪p≫
   name_pointer p ← rlink[0];	// current node of the search tree; ≪rlink[0]≫ is the root of the tree
   while (p ≠ 0) {
      c ← MatchNames(p, l); // Set ≪c≫ to the result of comparing the given name to name ≪p≫
      q ← p;
      if (c ≡ less) p ← llink[q];
      else if (c ≡ greater) p ← rlink[q];
      else break;
   }
   if (p ≡ 0) {
   // ‡7.3: Enter a new module name into the tree
      enum {ww} w ← name_ptr%ww;	// segment of ≪byte_mem[]≫
      enum {0..max_bytes} k ← byte_ptr[w];	// index into ≪byte_mem[]≫
      if (k + l > max_bytes) overflow("byte memory");
      if (name_ptr > max_names - ww) overflow("name");
      p ← name_ptr;
      if (c ≡ less) llink[q] ← p; else rlink[q] ← p;
      llink[p] ← 0, rlink[p] ← 0, c ← equal, equiv[p] ← 0;
      for (enum {0..longest_name} j ← 1 ⋯ l) byte_mem[w][k + j - 1] ← mod_text[j];
      byte_start[name_ptr↑ + ww] ← byte_ptr[w] ← k + l;
   // 7.3‡
   }
   if (c ≠ equal) err_print("! Incompatible section names"), p ← 0;
   return p;
}
// 7.2‡7.4: Set ≪c≫ to the result of comparing the given name to name ≪p≫
// Editor's Note:
// ∙	This was orginally a multiply-used module.
enum {less.extension} MatchNames(name_pointer p, sixteen_bits l) {
   enum {0..max_bytes} k ← byte_start[p];	// index into ≪byte_mem[]≫
   enum {less..extension} c ← equal;
   enum {ww} w ← p%ww;	// segment of ≪byte_mem[]≫
   enum {0..longest_name} j ← 1;	// index into ≪mod_text≫
   for (; k < byte_start[p + ww] ∧ j ≤ l ∧ mod_text[j] ≡ byte_mem[w][k]; k↑, j↑);
   return
      k ≡ byte_start[p + ww]? j > l? equal: extension:
      j > l? prefix:
      mod_text[j] < byte_mem[w][k]? less: greater;
}
// 7.4‡7.5:
// The ≪prefix_lookup()≫ procedure is supposed to find exactly one module name that has ≪mod_text[1..l]≫ as a prefix.
// Actually the algorithm silently accepts also the situation that some module name is a prefix of ≪mod_text[1..l]≫,
// because the user who painstakingly typed in more than necessary probably doesn't want to be told about the wasted effort.
name_pointer prefix_lookup(sixteen_bits l) {	// finds name extension
   name_pointer q ← 0;	// another place to resume the search after one branch is done
   name_pointer p ← rlink[0];	// current node of the search tree
   enum {0..max_names} count ← 0;	// the number of hits
   name_pointer r ← 0;	// extension found; begin search at root of tree
   while (p ≠ 0) {
      enum {less..extension} c ← MatchNames(p, l);	// The result of comparing the given name to name ≪p≫
      if (c ≡ less) p ← llink[p];
      else if (c ≡ greater) p ← rlink[p];
      else r ← p, count↑, q ← rlink[p], p ← llink[p];
      if (p ≡ 0) p ← q, q ← 0;
   }
   if (count ≡ 0) err_print("! Name does not match");
   else if (count ≠ 1) err_print("! Ambiguous prefix");
   return r;	// the result will be 0 if there was no match
}
// 7.5‡

// §8. Tokens.
// ‡8.1: Globals in the outer block (13/28)
// Replacement texts, which represent «Pas» code in a compressed format, appear in ≪tok_mem[]≫ as mentioned above.
// The codes in these texts are called ‛tokens’; some tokens occupy two consecutive eight-bit byte positions, and the others take just one byte.

// If $p > 0$ points to a replacement text, ≪tok_start[p]≫ is the ≪tok_mem[]≫ position of the first eight-bit code of that text.
// If ≪text_link[p] ≡ 0≫, this is the replacement text for a macro, otherwise it is the replacement text for a module.
// In the latter case ≪text_link[p]≫ is either equal to ≪module_flag≫, which means that there is no further text for this module,
// or ≪text_link[p]≫ points to a continuation of this replacement text;
// such links are created when several modules have «Pas» texts with the same name, and they also tie together all the «Pas» texts of unnamed modules.
// The replacement text pointer for the first unnamed module appears in ≪text_link[0]≫, and the most recent such pointer is ≪last_unnamed≫.
#define module_flag max_texts	// final ≪text_link≫ in module replacement texts

// ‡8.2: Set initial values (11/14) [continued]
text_pointer last_unnamed ← 0;	// most recent replacement text of unnamed module
// 8.2‡
// 8.1‡8.3:
// If the first byte of a token is less than 0x80, the token occupies a single byte.
// Otherwise we make a sixteen-bit token by combining two consecutive bytes ≪a≫ and ≪b≫.
// If ≪0x80 ≤ a < 0xa8≫, then $(a - 0x80)×2^8 + b$ points to an identifier;
// if (≪0xa8 ≤ a < 0xd0≫), $(a - 0xa8)×2^8 + b$ points to a module name;
// otherwise, i.e., if ≪0xd0 ≤ a < 0x100≫, then $(a - 0xd0)×2^8 + b$ is the number of the module in which the current replacement text appears.

// Codes less than 0x80 are 7-bit ASCII codes that represent themselves.
// In particular, a single-character identifier like ‛≪x≫’ will be a one-byte token, while all longer identifiers will occupy two bytes.

// Some of the 7-bit ASCII codes will not be present, however, so we can use them for special purposes.
// The following symbolic names are used:
// ∙	≪param≫ denotes insertion of a parameter.
//	This occurs only in the replacement texts of parametric macros, outside of single-quoted strings in those texts.
// ∙	≪begin_comment≫ denotes ‹@{›, which will become either ‹{› or ‹[›.
// ∙	≪end_comment≫ denotes ‹@}›, which will become either ‹}› or ‹]›.
// ∙	≪octal≫ denotes the ‹@'› that precedes an octal constant.
// ∙	≪hex≫ denotes the ‹@"› that precedes a hexadecimal constant.
// ∙	≪check_sum≫ denotes the ‹@‹char›'44› that denotes the string pool check sum.
// ∙	≪join≫ denotes the concatenation of adjacent items with no space or line breaks allowed between them (the ‹@&› operation of ‹WEB›).
// ∙	≪double_dot≫ denotes ‛‹..›’ in «Pas».
// ∙	≪verbatim≫ denotes the ‹@=› that begins a verbatim «Pas» string.
//	It is also used for the end of the string.
// ∙	≪force_line≫ denotes the ‹@\› that forces a new line in the «Pas» output.
#define param		0x00	// ASCII null code will not appear
#define verbatim	0x02	// extended ASCII alpha should not appear
#define force_line	0x03	// extended ASCII beta should not appear
#define begin_comment	0x09	// ASCII tab mark will not appear
#define end_comment	0x0a	// ASCII line feed will not appear
#define octal		0x0c	// ASCII form feed will not appear
#define hex		0x0d	// ASCII carriage return will not appear
#define double_dot	0x20	// ASCII space will not appear except in strings
#define check_sum	0x7d	// will not be confused with right brace
#define join		0x7f	// ASCII delete will not appear

// 8.3‡8.4:
// The following procedure is used to enter a two-byte value into ≪tok_mem[]≫ when a replacement text is being generated.
void store_two_bytes(sixteen_bits x) {	// stores high byte, then low byte
   if (tok_ptr[z] + 2 > max_toks) overflow("token");
   tok_mem[z][tok_ptr[z]] ← x/0x100;	// this could be done by a shift command
   tok_mem[z][tok_ptr[z] + 1] ← x%0x100;	// this could be done by a logical and
   tok_ptr[z] += 2;
}

// 8.4‡8.5:
// When ‹TANGLE› is being operated in debug mode, it has a procedure to display a replacement text in symbolic form.
// This procedure has not been spruced up to generate a real great format, but at least the results are not as bad as a memory dump.
#if DEBUG
void print_repl(text_pointer p) {
   if (p ≥ text_ptr) print("BAD");
   else {
      enum {0..max_toks} k ← tok_start[p];	// index into ≪tok_mem[]≫
      enum {zz} zp ← p%zz;	// segment of ≪tok_mem[]≫ being accessed
      for (; k < tok_start[p + zz]; k↑) {
         sixteen_bits a ← tok_mem[zp][k];	// current byte(s)
         if (a ≥ 0x80) {
         // ‡8.6: Display two-byte token starting with ≪a≫
            k↑;
            if (a < 0xa8) {	// identifier or string
               a ← 0x100*(a - 0x80) + tok_mem[zp][k], print_id(a);
               if (byte_mem[a%ww][byte_start[a]] ≡ '"') print("\""); else print(" ");
            } else if (a < 0xd0)	// module name
               print("@<"), print_id(0x100*(a - 0xa8) + tok_mem[zp][k]), print("@>");
            else
               a ← 0x100*(a - 0xd0) + tok_mem[zp][k],	// module number
               print("@{%1d@}", a);
         // 8.6‡
         } else
         // ‡8.7: Display one-byte token ≪a≫
            switch (a) {
               case begin_comment: print("@{"); break;
               case end_comment: print("@}"); break;
               case octal: print("@'"); break;
               case hex: print("@\""); break;
               case check_sum: print("@$"); break;
               case param: print("#"); break;
               case '@': print("@@"); break;
               case verbatim: print("@="); break;
               case force_line: print("@\\"); break;
               default: print(xchr[a]) break;
            }
         // 8.7‡
      }
   }
}
#endif // DEBUG
// 8.5‡

// §9. Stacks for Output.
// ‡9.1:
// Let's make sure that our data structures contain enough information to produce the entire «Pas» program as desired,
// by working next on the algorithms that actually do produce that program.

// 9.1‡9.2: Types in the outer block (6/6)
// The output process uses a stack to keep track of what is going on at different ‟levels” as the macros are being expanded.
// Entries on this stack have five parts:
// ∙	≪end_field≫ is the ≪tok_mem[]≫ location where the replacement text of a particular level will end;
// ∙	≪byte_field≫ is the ≪tok_mem[]≫ location from which the next token on a particular level will be read;
// ∙	≪name_field≫ points to the name corresponding to a particular level;
// ∙	≪repl_field≫ points to the replacement text currently being read at a particular level;
// ∙	≪mod_field≫ is the module number, or zero if this is a macro.
// The current values of these five quantities are referred to quite frequently,
// so they are stored in a separate place instead of in the ≪stack≫ array.
// We call the current values ≪cur_end≫, ≪cur_byte≫, ≪cur_name≫, ≪cur_repl≫, and ≪cur_mod≫.

// The global variable ≪stack_ptr≫ tells how many levels of output are currently in progress.
// The end of all output occurs when the stack is empty, i.e., when ≪stack_ptr ≡ 0≫.
typedef struct {
   sixteen_bits end_field;	// ending location of replacement text
   sixteen_bits byte_field;	// present location within replacement text
   name_pointer name_field;	// ≪byte_start≫ index for text being output
   text_pointer repl_field;	// ≪tok_start≫ index for text being output
   enum {0x3000} mod_field;	// module number or zero if not a module
} output_state;

// 9.2‡9.3: Globals in the outer block (14/28)
#define cur_end cur_state.end_field	// current ending location in ≪tok_mem[]≫
#define cur_byte cur_state.byte_field	// location of next output byte in ≪tok_mem[]≫
#define cur_name cur_state.name_field	// pointer to current name being expanded
#define cur_repl cur_state.repl_field	// pointer to current replacement text
#define cur_mod cur_state.mod_field	// current module number being expanded

output_state cur_state;	// ≪cur_end≫, ≪cur_byte≫, ≪cur_name≫, ≪cur_repl≫, ≪cur_mod≫
output_state stack[1..stack_size];	// info for non-current levels
enum {0..stack_size} stack_ptr;	// first unused location in the output state stack

// 9.3‡9.4: Globals in the outer block (15/28)
// It is convenient to keep a global variable ≪zo≫ equal to ≪cur_repl%zz≫.
enum {zz} zo;	// the segment of ≪tok_mem[]≫ from which output is coming

// 9.4‡9.5:
//Parameters must also be stacked.
//They are placed in ≪tok_mem[]≫ just above the other replacement texts,
//and dummy parameter ‛names’ are placed in ≪byte_start≫ just after the other names.
//The variables ≪text_ptr≫ and ≪tok_ptr[z]≫ essentially serve as parameter stack pointers during the output phase,
//so there is no need for a separate data structure to handle this problem.

// 9.5‡9.6: Globals in the outer block (16/28)
// There is an implicit stack corresponding to meta-comments that are output via ‹@{› and ‹@}›.
// But this stack need not be represented in detail, because we only need to know whether it is empty or not.
// A global variable ≪brace_level≫ tells how many items would be on this stack if it were present.
eight_bits brace_level;	// current depth of ‹@{›…‹@}› nesting

// 9.6‡9.8:
// When the replacement text for name ≪p≫ is to be inserted into the output,
// the following subroutine is called to save the old level of output and get the new one going.
void push_level(name_pointer p) {	// suspends the current level
   if (stack_ptr ≡ stack_size) overflow("stack");
   else {
      stack[stack_ptr↑] ← cur_state;	// save ≪cur_end≫, ≪cur_byte≫, etc.
      cur_name ← p, cur_repl ← equiv[p], zo ← cur_repl%zz;
      cur_byte ← tok_start[cur_repl], cur_end ← tok_start[cur_repl + zz];
      cur_mod ← 0;
   }
}

// 9.8‡9.9:
// When we come to the end of a replacement text, the ≪pop_level()≫ subroutine does the right thing:
// It either moves to the continuation of this replacement text or returns the state to the most recently stacked level.
// Part of this subroutine, which updates the parameter stack, will be given later when we study the parameter stack in more detail.
void pop_level(void) {	// do this when ≪cur_byte≫ reaches ≪cur_end≫
   if (text_link[cur_repl] ≡ 0) {	// end of macro expansion
      if (ilk[cur_name] ≡ parametric) {
      // ‡9.15: Remove a parameter from the parameter stack
      // The ≪pop_level()≫ routine undoes the effect of parameter-pushing when a parameter macro is finished:
         name_ptr↓, text_ptr↓;
         z ← text_ptr%zz;
#if STATS
         if (tok_ptr[z] > max_tok_ptr[z]) max_tok_ptr[z] ← tok_ptr[z];
#endif // STATS
      // the maximum value of ≪tok_ptr≫ occurs just before parameter popping
         tok_ptr[z] ← tok_start[text_ptr];
#if DEBUG
         byte_ptr[name_ptr%ww]↓;
#endif // DEBUG
      // 9.15‡
      }
   } else if (text_link[cur_repl] < module_flag) {	// link to a continuation
      cur_repl ← text_link[cur_repl];	// we will stay on the same level
      zo ← cur_repl%zz;
      cur_byte ← tok_start[cur_repl], cur_end ← tok_start[cur_repl + zz];
      return;
   }
// we will go down to the previous level
   if (↓stack_ptr > 0) cur_state ← stack[stack_ptr], zo ← cur_repl%zz;
}

// 9.9‡9.10: Globals in the outer block (17/28)
// The heart of the output procedure is the ≪get_output()≫ routine, which produces the next token of output that is not a reference to a macro.
// This procedure handles all the stacking and unstacking that is necessary.
// It returns the value ≪number≫ if the next output has a numeric value (the value of a numeric macro or string),
// in which case ≪cur_val≫ has been set to the number in question.
// The procedure also returns the value ≪module_number≫ if the next output begins or ends the replacement text of some module,
// in which case ≪cur_val≫ is that module's number (if beginning) or the negative of that value (if ending).
// And it returns the value ≪identifier≫ if the next output is an identifier of length two or more, in which case ≪cur_val≫ points to that identifier name.
#define number		0x80	// code returned by ≪get_output()≫ when next output is numeric
#define module_number	0x81	// code returned by ≪get_output()≫ for module numbers
#define identifier	0x82	// code returned by ≪get_output()≫ for identifiers

integer cur_val;	// additional information corresponding to output token

// 9.10‡9.11:
// If ≪get_output()≫ finds that no more output remains, it returns the value zero.
#if DEBUG
#   define Return(X)	return trouble_shooting? (debug_help(), (X)): (X)
#else
#   define Return(X)	return (X)
#endif

// ‡9.17: Copy the parameter into ≪tok_mem[]≫
inline void app_repl(eight_bits A) {
   if (tok_ptr[z] ≡ max_toks) overflow("token");
   tok_mem[z][tok_ptr[z]↑] ← A;
}
// 9.17‡

sixteen_bits get_output(void) {	// returns next token after macro expansion
   while (stack_ptr > 0) {
      while (cur_byte ≡ cur_end) {
         cur_val ← -cur_mod, pop_level();
         if (cur_val ≠ 0) Return(module_number);
      }
      sixteen_bits a ← tok_mem[zo][cur_byte↑];	// value of current byte
      if (a ≡ param)
      // ‡9.16: Start scanning current macro parameter
      // When a parameter occurs in a replacement text, we treat it as a simple macro in position (≪name_ptr - 1≫):
         push_level(name_ptr - 1);
      // 9.16‡
      else if (a < 0x80) Return(a);	// one-byte token
      if (a < 0xa8) {
         a ← 0x100*(a - 0x80) + tok_mem[zo][cur_byte↑];
      // ‡9.13: Expand macro ≪a≫ and return if output found
         switch (ilk[a]) {
            case normal: cur_val ← a; Return(identifier);
            case numeric: cur_val ← equiv[a] - 0x8000; Return(number);
            case simple: push_level(a); break;
            case parametric:
            // ‡9.14: Put a parameter on the parameter stack, or ≪continue;≫ if error occurs
            // We come now to the interesting part, the job of putting a parameter on the parameter stack.
            // First we pop the stack if necessary until getting to a level that hasn't ended.
            // Then the next character must be a ‛‹(›’;
            // and since parentheses are balanced on each level, the entire parameter must be present, so we can copy it without difficulty.
               while (cur_byte ≡ cur_end ∧ stack_ptr > 0) pop_level();
               if (stack_ptr ≡ 0 ∨ tok_mem[zo][cur_byte] ≠ '(') {
                  print("\n! No parameter given for "), print_id(a), error();
                  continue;
               }
            // ‡9.17: Copy the parameter into ≪tok_mem[]≫ [continued]
            // Similarly, a ≪param≫ token encountered as we copy a parameter is converted into a simple macro call for ≪name_ptr - 1≫.
            // Some care is needed to handle cases like \\{macro}≪(#; print("#)"))≫; the ‹#› token will have been changed to ≪param≫ outside of strings,
            // but we still must distinguish ‛real’ parentheses from those in strings.
               sixteen_bits bal ← 1; // excess of ‹(› versus ‹)› while copying a parameter
               cur_byte↑;	// skip the opening ‛‹(›’
               while (true) {
                  eight_bits b ← tok_mem[zo][cur_byte↑];	// byte being copied
                  if (b ≡ param) store_two_bytes(name_ptr + 0x7fff);
                  else {
                     if (b ≥ 0x80) app_repl(b), b ← tok_mem[zo][cur_byte↑];
                     else switch (b) {
                        case '(': bal↑; break;
                        case ')':
                           if (↓bal ≡ 0) goto done;
                        break;
                        case '\'':
                           do app_repl(b), b ← tok_mem[zo][cur_byte↑]; while (b ≠ '\'');	// copy string, don't change ≪bal≫
                        break;
                        default: break;
                     }
                     app_repl(b);
                  }
               }
            done:
            // 9.17‡
               equiv[name_ptr] ← text_ptr, ilk[name_ptr] ← simple;
               enum {ww} w ← name_ptr%ww;	// segment of ≪byte_mem[]≫
               enum {0..max_bytes} k ← byte_ptr[w];	// index into ≪byte_mem[]≫
#if DEBUG
               if (k ≡ max_bytes) overflow("byte memory");
               byte_mem[w][k↑] ← '#', byte_ptr[w] ← k;
#endif // DEBUG
            // this code has set the parameter identifier for debugging printouts
               if (name_ptr > max_names - ww) overflow("name");
               byte_start[name_ptr↑ + ww] ← k;
               if (text_ptr > max_texts - zz) overflow("text");
               text_link[text_ptr] ← 0, tok_start[text_ptr↑ + zz] ← tok_ptr[z];
               z ← text_ptr%zz;
            // 9.14‡
               push_level(a);
            break;
            default: confusion("output"); // break;
         }
      // 9.13‡
      } else if (a < 0xd0) {
         a ← 0x100*(a - 0xa8) + tok_mem[zo][cur_byte↑];
      // ‡9.12: Expand module ≪a≫
      // The user may have forgotten to give any «Pas» text for a module name, or the «Pas» text may have been associated with a different name by mistake.
         if (equiv[a] ≠ 0) push_level(a);
         else if (a ≠ 0) print("\n! Not present: <"), print_id(a), print(">"), error();
      // 9.12‡
      } else {
         cur_mod ← cur_val ← 0x100*(a - 0xd0) + tok_mem[zo][cur_byte↑]; Return(module_number);
      }
   }
   Return(0);
}
// 9.11‡

// §10. Producing the Output.
// ‡10.1: Globals in the outer block (18/28)
// The ≪get_output()≫ routine above handles most of the complexity of output generation,
// but there are two further considerations that have a nontrivial effect on ‹TANGLE›'s algorithms.

// First, we want to make sure that the output is broken into lines not exceeding ≪line_length≫ characters per line,
// where these breaks occur at valid places
// (e.g., not in the middle of a string or a constant or an identifier, not between ‛‹<›’ and ‛‹>›’,
// not at a ‛‹@&›’ position where quantities are being joined together).
// Therefore we assemble the output into a buffer before deciding where the line breaks will appear.
// However, we make very little attempt to make ‟logical” line breaks that would enhance the readability of the output;
// people are supposed to read the input of ‹TANGLE› or the «TeX» ed output of ‹WEAVE›, but not the tangled-up output.
// The only concession to readability is that a break after a semicolon will be made if possible,
// since commonly used ‟pretty printing” routines give better results in such cases.

// Second, we want to decimalize non-decimal constants, and to combine integer quantities that are added or subtracted,
// because «Pas» doesn't allow constant expressions in subrange types or in case labels.
// This means we want to have a procedure that treats a construction like ‹(E - 15 + 17)› as equivalent to ‛‹(E + 2)›’,
// while also leaving ‛‹(1E - 15 + 17)›’ and ‛‹(E - 15 + 17*y)›’ untouched.
// Consider also ‛‹-15 + 17.5›’ versus ‛‹-15 + 17..5›’. We shall not combine integers preceding or following ‹*›, ‹/›, ‹/›, ‹%›, or ‹@&›.
// Note that if ≪y≫ has been defined to equal $-2$, we must expand ‛‹x*y›’ into ‛‹x*(-2)›’;
// but ‛‹x - y›’ can expand into ‛‹x + 2›’ and we can even change ‛‹x - y%z›’ to ‛‹x + 2%z›’ because «Pas» has a nonstandard ‹·%·» operation!

// The following solution to these problems has been adopted:
// An array ≪out_buf≫ contains characters that have been generated but not yet output, and there are three pointers into this array.
// One of these, ≪out_ptr≫, is the number of characters currently in the buffer, and we will have ≪1 ≤ out_ptr ≤ line_length≫ most of the time.
// The second is ≪break_ptr≫, which is the largest value ≪ ≤ out_ptr≫
// such that we are definitely entitled to end a line by outputting the characters ≪out_buf[1..(break_ptr - 1)]≫;
// we will always have ≪break_ptr ≤ line_length≫.
// Finally, ≪semi_ptr≫ is either zero or the largest known value of a legal break after a semicolon or comment on the current line;
// we will always have ≪semi_ptr ≤ break_ptr≫.
ASCII_code out_buf[0..out_buf_size];	// assembled characters
enum {0..out_buf_size} out_ptr;		// first available place in ≪out_buf≫
enum {0..out_buf_size} break_ptr;	// last breaking place in ≪out_buf≫
enum {0..out_buf_size} semi_ptr;	// last semicolon breaking place in ≪out_buf≫

// 10.1‡10.2: Globals in the outer block (19/28)
// Besides having those three pointers, the output process is in one of several states:
// ∙	≪num_or_id≫ means that the last item in the buffer is a number or identifier,
//	hence a blank space or line break must be inserted if the next item is also a number or identifier.
// ∙	≪unbreakable≫ means that the last item in the buffer was followed by the ‹@&› operation that inhibits spaces between it and the next item.
// ∙	≪sign≫ means that the last item in the buffer is to be followed by ‹+› or ‹-›, depending on whether ≪out_app≫ is positive or negative.
// ∙	≪sign_val≫ means that the decimal equivalent of $‹vert›≪out_val≫‹vert›$ should be appended to the buffer.
//	If ≪out_val < 0≫, or if ≪out_val ≡ 0≫ and ≪last_sign < 0≫, the number should be preceded by a minus sign.
//	Otherwise it should be preceded by the character ≪out_sign≫ unless ≪out_sign ≡ 0≫; the ≪out_sign≫ variable is either 0 or ‹' '› or ‹'+'›.
// ∙	≪sign_val_sign≫ is like ≪sign_val≫, but also append ‹+› or ‹-› afterwards, depending on whether ≪out_app≫ is positive or negative.
// ∙	≪sign_val_val≫ is like ≪sign_val≫, but also append the decimal equivalent of ≪out_app≫ including its sign, using ≪last_sign≫ in case ≪out_app ≡ 0≫.
// ∙	≪misc≫ means none of the above.
// For example, the output buffer and output state run through the following sequence as we generate characters from ‛‹(x - 15 + 19 - 2)›’:
//	output	out_buf	out_state	out_sign	out_val	out_app	last_sign
//	(	(	misc
//	x	(x	num_or_id
//	-	(x	sign				-1	-1
//	15	(x	sign_val	+		-15		-15
//	+	(x	sign_val_sign	+		-15	+1	+1
//	19	(x	sign_val_val	+		-15	+19	+1
//	-	(x	sign_val_sign	+		+4	-1	-1
//	2	(x	sign_val_val	+		+4	-2	-2
//	)	(x + 2)	misc
// At each stage we have put as much into the buffer as possible without knowing what is coming next.
// Examples like ‛‹x - 0.1›’ indicate why ≪last_sign≫ is needed to associate the proper sign with an output of zero.

// In states ≪num_or_id≫, ≪unbreakable≫, and ≪misc≫ the last item in the buffer lies between ≪break_ptr≫ and ≪out_ptr - 1≫, inclusive;
// in the other states we have ≪break_ptr ≡ out_ptr≫.

// The numeric values assigned to ≪num_or_id≫, etc., have been chosen to shorten some of the program logic;
// for example, the program makes use of the fact that ≪sign + 2 ≡ sign_val_sign≫.
#define misc		0	// state associated with special characters
#define num_or_id	1	// state associated with numbers and identifiers
#define sign		2	// state associated with pending ‹+› or ‹-›
#define sign_val	3	// state associated with pending sign and value
#define sign_val_sign	4	// ≪sign_val≫ followed by another pending sign
#define sign_val_val	sign_val + 2	// ≪sign_val≫ followed by another pending value
#define unbreakable	sign_val_val + 1	// state associated with ‹@&›

eight_bits out_state;		// current status of partial output
integer out_val, out_app;	// pending values
ASCII_code out_sign;		// sign to use if appending ≪out_val ≥ 0≫
enum {-1..+1} last_sign;	// sign to use if appending a zero

// 10.2‡10.4:
// Here is a routine that is invoked when ≪out_ptr > line_length≫ or when it is time to flush out the final line.
// The ≪flush_buffer()≫ procedure often writes out the line up to the current ≪break_ptr≫ position,
// then moves the remaining information to the front of ≪out_buf≫. However, it prefers to write only up to ≪semi_ptr≫,
// if the residual line won't be too long.
inline void check_break(void) {
   if (out_ptr > line_length) flush_buffer();
}

void flush_buffer(void) {	// writes one line to output file
   enum {0..out_buf_size} b ← break_ptr;	// value of ≪break_ptr≫ upon entry
   if (semi_ptr ≠ 0 ∧ out_ptr-semi_ptr ≤ line_length) break_ptr ← semi_ptr;
   for (enum {0..out_buf_size} k ∈ break_ptr) write(Pascal_file, "%c", xchr[out_buf[k]]);
   write(Pascal_file, "\n"), line↑;
   if (line%100 ≡ 0) {
      print(".");
      if (line%500 ≡ 0) print("%1d", line);
      update_terminal();	// progress report
   }
   if (break_ptr < out_ptr) {
      if (out_buf[break_ptr] ≡ ' ') {
         if (↑break_ptr > b) b ← break_ptr;	// drop space at break
      }
      for (enum {0..out_buf_size} k ← break_ptr ⋯ out_ptr - 1) out_buf[k - break_ptr] ← out_buf[k];
   }
   out_ptr -= break_ptr, break_ptr ← b - break_ptr, semi_ptr ← 0;
   if (out_ptr > line_length) err_print("! Long line must be truncated"), out_ptr ← line_length;
}
// 10.4‡

‡10.6:
Another simple and useful routine appends the decimal equivalent of a nonnegative integer to the output buffer.

inline void app(ASCII_code A) { out_buf[out_ptr↑] ← A; }	// append a single character

¶
void app_val(integer v) {	// puts ≪v≫ into buffer, assumes ≪v ≥ 0≫
   enum {0..out_buf_size} k ← out_buf_size;	// index into ≪out_buf≫
// first we put the digits at the very end of ≪out_buf≫
   do out_buf[k↓] ← v%10, v /= 10; while (v ≠ 0);
// then we append them, most significant first
   do app(out_buf[↑k] + '0'); while (k ≠ out_buf_size);
}

// ‡10.7: Globals in the outer block (20/28)
// The output states are kept up to date by the output routines, which are called ≪send_out()≫, ≪send_val()≫, and ≪send_sign()≫.
// The ≪send_out()≫ procedure has two parameters: ≪t≫ tells the type of information being sent and ≪v≫ contains the information proper.
// Some information may also be passed in the array ≪out_contrib≫.
// ∙	If ≪t ≡ misc≫ then ≪v≫ is a character to be output.
// ∙	If ≪t ≡ str≫ then ≪v≫ is the length of a string or something like ‛‹<>›’ in ≪out_contrib≫.
// ∙	If ≪t ≡ ident≫ then ≪v≫ is the length of an identifier in ≪out_contrib≫.
// ∙	If ≪t ≡ frac≫ then ≪v≫ is the length of a fraction and/or exponent in ≪out_contrib≫.
#define str	1	// ≪send_out()≫ code for a string
#define ident	2	// ≪send_out()≫ code for an identifier
#define frac	3	// ≪send_out()≫ code for a fraction

ASCII_code out_contrib[1..line_length];	// a contribution to ≪out_buf≫

// 10.7‡10.8:
// A slightly subtle point in the following code is that the user may ask for a ≪join≫ operation (i.e., ‹@&›)
// following whatever is being sent out.
// We will see later that ≪join≫ is implemented in part by calling ≪send_out(frac, 0)≫.
void send_out(eight_bits t, sixteen_bits v) {	// outputs ≪v≫ of type ≪t≫
// ‡10.9: Get the buffer ready for appending the new information
// Here is where the buffer states for signs and values collapse into simpler states,
// because we are about to append something that doesn't combine with the previous integer constants.

// We use an ASCII-code trick: Since ≪',' - 1 ≡ '+'≫ and ≪',' + 1 ≡ '-'≫, we have ≪',' - c ≡ ‹ sign of c›≫, when ‹vert› c‹vert› ≡ 1.
   switch (out_state) {
      case sign_val_val:
      // ‡10.11: Reduce ≪sign_val_val≫ to ≪sign_val≫
         if (t ≡ frac ∨
         // ‡10.12: Contribution is ‹*› or ‹/› or ‹DIV› or ‹MOD›
            t ≡ ident ∧ v ≡ 3 ∧ (
               out_contrib[1] ≡ 'D' ∧ out_contrib[2] ≡ 'I' ∧ out_contrib[3] ≡ 'V' ∨
               out_contrib[1] ≡ 'M' ∧ out_contrib[2] ≡ 'O' ∧ out_contrib[3] ≡ 'D'
            ) ∨ t ≡ misc ∧ (v ≡ '*' ∨ v ≡ '/')
         // 10.12‡
         ) {
            BufferOutVal(); // Append ≪out_val≫ to buffer
            out_sign ← '+', out_val ← out_app;
         } else out_val += out_app;
      // 10.11‡
         out_state ← sign_val;
      case sign_val:
         BufferOutVal(); // Append ≪out_val≫ to buffer
         out_state = num_or_id;
      case num_or_id:
         if (t ≠ frac) {
            break_ptr ← out_ptr;
            if (t ≡ ident) app(' ');
         }
      break;
      case sign_val_sign:
         BufferOutVal(); // Append ≪out_val≫ to buffer
         out_state = sign;
      case sign:
         app(',' - out_app), check_break(), break_ptr ← out_ptr;
      break;
      case misc:
         if (t ≠ frac) break_ptr ← out_ptr;
      break;
      default: break;	// this is for ≪unbreakable≫ state
   }
// 10.9‡
   if (t ≠ misc) for (enum {0..line_length} k ← 1 ⋯ v) app(out_contrib[k]);
   else app(v);
   check_break();
   if (t ≡ misc ∧ (v ≡ ';' ∨ v ≡ '}')) semi_ptr ← out_ptr, break_ptr ← out_ptr;
   out_state ←
      t ≥ ident? num_or_id:	// ≪t ≡ ident≫ or ≪frac≫
      misc	// ≪t ≡ str≫ or ≪misc≫
}

// 10.8‡10.10: Append ≪out_val≫ to buffer
// Editor's Note:
// ∙	This was orginally a multiply-used module.
inline void BufferOutVal(void) {
   if (out_val < 0 ∨ out_val ≡ 0 ∧ last_sign < 0) app('-');
   else if (out_sign > 0) app(out_sign);
   app_val(abs(out_val)), check_break();
}

// 10.10‡10.13:
// The following routine is called with $v ≡ ±1$ when a plus or minus sign is appended to the output.
// It extends «Pas» to allow repeated signs (e.g., ‛‹--›’ is equivalent to ‛‹+›’), rather than to give an error message.
// The signs following ‛‹E›’ in real constants are treated as part of a fraction, so they are not seen by this routine.
void send_sign(integer v) {
   switch (out_state) {
      case sign: case sign_val_sign: out_app *= v; break;
      case sign_val: out_app ← v, out_state ← sign_val_sign; break;
      case sign_val_val: out_val += out_app, out_app ← v, out_state ← sign_val_sign; break;
      default: break_ptr ← out_ptr, out_app ← v, out_state ← sign; break;
   }
   last_sign ← out_app;
}

// 10.13‡10.14:
// When a (signed) integer value is to be output, we call ≪send_val()≫.
void send_val(integer v) {	// output the (signed) value ≪v≫
   switch (out_state) {
      case num_or_id:
      // ‡10.17: If previous output was ‹DIV› or ‹MOD›, ≪goto bad_case≫
         if (out_ptr ≡ break_ptr + 3 ∨ out_ptr ≡ break_ptr + 4 ∧ out_buf[break_ptr] ≡ ' ')
            if (
               out_buf[out_ptr - 3] ≡ 'D' ∧ out_buf[out_ptr - 2] ≡ 'I' ∧ out_buf[out_ptr - 1] ≡ 'V' ∨
               out_buf[out_ptr - 3] ≡ 'M' ∧ out_buf[out_ptr - 2] ≡ 'O' ∧ out_buf[out_ptr - 1] ≡ 'D'
            ) goto bad_case;
      // 10.17‡
         out_sign ← ' ', out_state ← sign_val, out_val ← v, break_ptr ← out_ptr,
         last_sign ← +1;
      break;
      case misc:
      // ‡10.16: If previous output was ‹*› or ‹/›, ≪goto bad_case≫
         if (out_ptr ≡ break_ptr + 1 ∧ (out_buf[break_ptr] ≡ '*' ∨ out_buf[break_ptr] ≡ '/')) goto bad_case;
      // 10.16‡
         out_sign ← 0, out_state ← sign_val, out_val ← v, break_ptr ← out_ptr,
         last_sign ← +1;
      break;
   // ‡10.15: Handle cases of ≪send_val()≫ when ≪out_state≫ contains a sign
      case sign: out_sign ← '+', out_state ← sign_val, out_val ← out_app*v; break;
      case sign_val: out_state ← sign_val_val, out_app ← v, err_print("! Two numbers occurred without a sign between them"); break;
      case sign_val_sign: out_state ← sign_val_val, out_app *= v; break;
      case sign_val_val: out_val += out_app, out_app ← v, err_print("! Two numbers occurred without a sign between them"); break;
   // 10.15‡
      default:
      bad_case:	// go here if we can't keep ≪v≫ in the output state
      // ‡10.18: Append the decimal value of ≪v≫, with parentheses if negative
         if (v ≥ 0) {
            if (out_state ≡ num_or_id) break_ptr ← out_ptr, app(' ');
            app_val(v), check_break(), out_state ← num_or_id;
         } else app('('), app('-'), app_val(-v), app(')'), check_break(), out_state ← misc;
      // 10.18‡
      break;
   }
}
// 10.14‡

// §11. The big Output Switch.
// ‡11.2:
// A many-way switch is used to send the output:
void send_the_output(void) {
   while (stack_ptr > 0) {
      eight_bits cur_char ← get_output();	// the latest character received
   reswitch:
      switch (cur_char) {
         enum {0..line_length} k;	// index into ≪out_contrib≫
         case 0: break;	// this case might arise if output ends unexpectedly
      // ‡11.5: Cases related to identifiers
      // Single-character identifiers represent themselves, while longer ones appear in ≪byte_mem[]≫.
      // All must be converted to uppercase, with underlines removed. Extremely long identifiers must be chopped.
      //
      // (Some «Pas» compilers work with lowercase letters instead of uppercase.
      // If this module of ‹TANGLE› is changed,
      // it's also necessary to change from uppercase to lowercase in the modules that are listed in the index under ‟uppercase”.)
      // (#) system dependencies
         case 'A': case 'B': case 'C': case 'D': case 'E': case 'F': case 'G': case 'H': case 'I': case 'J': case 'K': case 'L': case 'M':
         case 'N': case 'O': case 'P': case 'Q': case 'R': case 'S': case 'T': case 'U': case 'V': case 'W': case 'X': case 'Y': case 'Z':
            out_contrib[1] ← cur_char, send_out(ident, 1);
         break;
         case 'a': case 'b': case 'c': case 'd': case 'e': case 'f': case 'g': case 'h': case 'i': case 'j': case 'k': case 'l': case 'm':
         case 'n': case 'o': case 'p': case 'q': case 'r': case 's': case 't': case 'u': case 'v': case 'w': case 'x': case 'y': case 'z':
            out_contrib[1] ← cur_char - 0x20, send_out(ident, 1);
         break;
         case identifier: {
            enum {0..max_bytes} j ← byte_start[cur_val];	// index into ≪byte_mem[]≫
            enum {ww} w ← cur_val%ww;	// segment of ≪byte_mem[]≫
            enum {0..line_length} k ← 0;	// index into ≪out_contrib≫
            while (k < max_id_length ∧ j < byte_start[cur_val + ww]) {
               out_contrib[↑k] ← byte_mem[w][j↑];
               if (out_contrib[k] ≥ 'a') out_contrib[k] -= 0x20;
               else if (out_contrib[k] ≡ '_') k↓;
            }
            send_out(ident, k);
         }
         break;
      // 11.5‡11.8: Cases related to constants, possibly leading to ≪get_fraction≫ or ≪goto reswitch
      // In order to encourage portable software, ‹TANGLE› complains
      // if the constants get dangerously close to the largest value representable on a 32-bit computer ($2^{31} - 1$).
         case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9': {
            integer n ← 0;	// number being scanned
            do {
               cur_char -= '0';
               if (n ≥ 0xccccccc) err_print("! Constant too big");
               else n ← 10*n + cur_char;
               cur_char ← get_output();
            } while (cur_char ≤ '9' ∧ cur_char ≥ '0');
            send_val(n), k ← 0;
            if (cur_char ≡ 'e') cur_char ← 'E';
            if (cur_char ≡ 'E') goto get_fraction;
         }
         goto reswitch;
         case check_sum: send_val(pool_check_sum); break;
         case octal: {
            integer n ← 0;	// number being scanned
            cur_char ← '0';
            do {
               cur_char -= '0';
               if (n ≥ 0x10000000) err_print("! Constant too big");
               else n ← 010*n + cur_char;
               cur_char ← get_output();
            } while (cur_char ≤ '7' ∧ cur_char ≥ '0');
            send_val(n);
         }
         goto reswitch;
         case hex: {
            integer n ← 0;	// number being scanned
            cur_char ← '0';
            do {
               if (cur_char ≥ 'A') cur_char += 10 - 'A';
               else cur_char -= '0';
               if (n ≥ 0x8000000) err_print("! Constant too big");
               else n ← 0x10*n + cur_char;
               cur_char ← get_output();
            } while (cur_char ≤ 'F' ∧ cur_char ≥ '0' ∧ (cur_char ≤ '9' ∨ cur_char ≥ 'A'));
            send_val(n);
         }
         goto reswitch;
         case number: send_val(cur_val); break;
         case '.':
            k ← 1, out_contrib[1] ← '.', cur_char ← get_output();
            if (cur_char ≡ '.') out_contrib[2] ← '.', send_out(str, 2);
            else if (cur_char ≥ '0' ∧ cur_char ≤ '9') goto get_fraction;
            else { send_out(misc, '.'); goto reswitch; }
         break;
      // 11.8‡
         case '+': case '-': send_sign(',' - cur_char); break;
      // ‡11.3: Cases like ‹<>› and ‹:=›
         case and_sign: out_contrib[1] ← 'A', out_contrib[2] ← 'N', out_contrib[3] ← 'D', send_out(ident, 3); break;
         case not_sign: out_contrib[1] ← 'N', out_contrib[2] ← 'O', out_contrib[3] ← 'T', send_out(ident, 3); break;
         case set_element_sign: out_contrib[1] ← 'I', out_contrib[2] ← 'N', send_out(ident, 2); break;
         case or_sign: out_contrib[1] ← 'O', out_contrib[2] ← 'R', send_out(ident, 2); break;
         case left_arrow: out_contrib[1] ← ':', out_contrib[2] ← '=', send_out(str, 2); break;
         case not_equal: out_contrib[1] ← '<', out_contrib[2] ← '>', send_out(str, 2); break;
         case less_or_equal: out_contrib[1] ← '<', out_contrib[2] ← '=', send_out(str, 2); break;
         case greater_or_equal: out_contrib[1] ← '>', out_contrib[2] ← '=', send_out(str, 2); break;
         case equivalence_sign: out_contrib[1] ← '=', out_contrib[2] ← '=', send_out(str, 2); break;
         case double_dot: out_contrib[1] ← '.', out_contrib[2] ← '.', send_out(str, 2); break;
      // 11.3‡
         case '\'': {
         // ‡11.6: Send a string
         // After sending a string, we need to look ahead at the next character, in order to see if there were two consecutive single-quote marks.
         // Afterwards we go to ≪reswitch≫ to process the next character.
            enum {0..line_length} k ← 1;	// index into ≪out_contrib≫
            out_contrib[1] ← '\'';
            do {
               if (k < line_length) k↑;
               out_contrib[k] ← get_output();
            } while (out_contrib[k] ≠ '\'' ∧ stack_ptr ≠ 0);
            if (k ≡ line_length) err_print("! String too long");
            send_out(str, k); cur_char ← get_output();
            if (cur_char ≡ '\'') out_state ← unbreakable;
         // 11.6‡
         }
         goto reswitch;
      // ‡11.4: Other printable characters
      // Please don't ask how all of the following characters can actually get through ‹TANGLE› outside of strings.
      // It seems that ≪'"'≫ and ≪'{'≫ cannot actually occur at this point of the program, but they have been included just in case ‹TANGLE› changes.
      //
      // If ‹TANGLE› is producing code for a «Pas» compiler that uses ‛‹(.›’ and ‛‹.)›’ instead of square brackets (e.g., on machines with ≪EBCDIC≫ code),
      // one should remove ≪'['≫ and ≪']'≫ from this list and put them into the preceding module in the appropriate way.
      // Similarly, some compilers want ‛‹^›’ to be converted to ‛‹@›’.
      // (#) system dependencies
         case '!': case '\'': case '#': case '$': case '%': case '&': case '(': case ')': case '*': case ',': case '/': case ':': case ';':
         case '<': case '=': case '>': case '?': case '@': case '[': case '\': case ']': case '^': case '_': case '`': case '{': case '|':
      // 11.4‡
            send_out(misc, cur_char);
         break;
      // ‡11.10: Cases involving ‹@{› and ‹@}›
      // Some «Pas» compilers do not recognize comments in braces, so the comments must be delimited by ‛‹(*›’ and ‛‹*)›’.
      // (#) system dependencies
      // In such cases the statement ‛≪out_contrib[1] ← '{'≫’ that appears here
      // should be replaced by ‛‹ignorespaces›≪(out_contrib[1] ← '(', out_contrib[2] ← '*', k↑)≫’,
      // and a similar change should be made to ‛≪out_contrib[k] ← '}'≫’.
         case begin_comment: send_out(misc, brace_level↑ ≡ 0? '{': '['); break;
         case end_comment:
            if (brace_level > 0) send_out(misc, ↓brace_level ≡ 0? '}': ']');
            else err_print("! Extra @}");
         break;
         case module_number: {
            enum {0..line_length} k ← 2;	// index into ≪out_contrib≫
            out_contrib[1] ← brace_level ≡ 0? '{': '[';
            if (cur_val < 0) out_contrib[k↑] ← ':', cur_val ← -cur_val;
            n ← 10;
            while (cur_val ≥ n) n *= 10;
            do n /= 10, out_contrib[k↑] ← '0' + cur_val/n, cur_val %= n; while (n ≠ 1);
            if (out_contrib[2] ≠ ':') out_contrib[k↑] ← ':';
            out_contrib[k] ← brace_level ≡ 0? '}': ']';
            send_out(str, k);
         }
         break;
      // 11.10‡
         case join: send_out(frac, 0), out_state ← unbreakable; break;
         case verbatim: {
         // ‡11.7: Send verbatim string
         // Sending a verbatim string is similar, but we don't have to look ahead.
            enum {0..line_length} k ← 0;	// index into ≪out_contrib≫
            do {
               if (k < line_length) k↑;
               out_contrib[k] ← get_output();
            } while (out_contrib[k] ≠ verbatim ∧ stack_ptr ≠ 0);
            if (k ≡ line_length) err_print("! Verbatim string too long");
            send_out(str, k↓);
         // 11.7‡
         }
         break;
         case force_line:
         // ‡11.11: Force a line break
            send_out(str, 0);	// normalize the buffer
            while (out_ptr > 0) {
               if (out_ptr ≤ line_length) break_ptr ← out_ptr;
               flush_buffer();
            }
            out_state ← misc;
         // 11.11‡
         break;
         default: err_print("! Can't output ASCII code %1d", cur_char); break;
         get_fraction: // go here to finish scanning a real constant
         // ‡11.9: Special code to finish real constants
         // The following code appears at label ‛≪get_fraction≫’, when we want to scan to the end of a real constant.
         // The first ≪k≫ characters of a fraction have already been placed in ≪out_contrib≫, and ≪cur_char≫ is the next character.
            do {
               if (k < line_length) k↑;
               out_contrib[k] ← cur_char, cur_char ← get_output();
               if (out_contrib[k] ≡ 'E' ∧ (cur_char ≡ '+' ∨ cur_char ≡ '-')) {
                  if (k < line_length) k↑;
                  out_contrib[k] ← cur_char; cur_char ← get_output();
               } else if (cur_char ≡ 'e') cur_char ← 'E';
            } while (cur_char ≡ 'E' ∨ cur_char ≥ '0' ∧ cur_char ≤ '9');
            if (k ≡ line_length) err_print("! Fraction too long");
            send_out(frac, k);
         // 11.9‡
         goto reswitch
      }
   }
}
// 11.2‡

// §12. Introduction to the Input Phase.
// ‡12.1:
// We have now seen that ‹TANGLE› will be able to output the full «Pas» program,
// if we can only get that program into the byte memory in the proper format.
// The input process is something like the output process in reverse, since we compress the text as we read it in and we expand it as we write it out.

// There are three main input routines. The most interesting is the one that gets the next token of a «Pas» text;
// the other two are used to scan rapidly past «TeX» text in the ‹WEB› source code.
// One of the latter routines will jump to the next token that starts with ‛‹@›’, and the other skips to the end of a «Pas» comment.

// 12.1‡12.2: Globals in the outer block (21/28)
// But first we need to consider the low-level routine ≪get_line()≫ that takes care of merging ≪change_file≫ into ≪web_file≫.
// The ≪get_line()≫ procedure also updates the line numbers for error messages.
integer ii;			// general purpose ≪for≫ loop variable in the outer block
integer line;			// the number of the current line in the current file
integer other_line;		// the number of the current line in the input file that is not currently being read
integer temp_line;		// used when interchanging ≪line≫ with ≪other_line≫
enum {0..buf_size} limit;	// the last character position occupied in the buffer
enum {0..buf_size} loc;		// the next character position to be read from the buffer
boolean input_has_ended;	// if ≪true≫, there is no more input
boolean changing;		// if ≪true≫, the current line is from ≪change_file≫

// 12.2‡12.3:
// As we change ≪changing≫ from ≪true≫ to ≪false≫ and back again,
// we must remember to swap the values of ≪line≫ and ≪other_line≫ so that the ≪err_print≫ routine will be sure to report the correct line number.
inline void change_changing(void) {
   changing ← !changing;
   temp_line ← other_line, other_line ← line, line ← temp_line;	// ≪line ‹‹null› ⇒ ‹null›› other_line≫
}

// 12.3‡12.4: Globals in the outer block (22/28)
// When ≪changing≫ is ≪false≫, the next line of ≪change_file≫ is kept in ≪change_buffer[0..change_limit]≫,
// for purposes of comparison with the next line of ≪web_file≫.
// After the change file has been completely input, we set ≪change_limit ← 0≫, so that no further matches will be made.
ASCII_code change_buffer[0..buf_size];
enum {0..buf_size} change_limit;	// the last position occupied in ≪change_buffer≫

// 12.4‡12.5:
// Here's a simple function that checks if the two buffers are different.
boolean lines_dont_match(void) {
   if (change_limit ≠ limit) return true;
   if (limit > 0) for (enum {0..buf_size} k ∈ limit) if (change_buffer[k] ≠ buffer[k]) return true;
   return false;
}

// 12.5‡12.6:
// Procedure ≪prime_the_change_buffer()≫ sets ≪change_buffer≫ in preparation for the next matching operation.
// Since blank lines in the change file are not used for matching, we have ≪(change_limit ≡ 0)and !changing≫
// if and only if the change file is exhausted.
// This procedure is called only when ≪changing≫ is true; hence error messages will be reported correctly.
void prime_the_change_buffer(void) {
   change_limit ← 0;	// this value will be used if the change file ends
// ‡12.7: Skip over comment lines in the change file; ≪return≫ if end of file
// While looking for a line that begins with ‹@x› in the change file, we allow lines that begin with ‹@›,
// as long as they don't begin with ‹@y› or ‹@z› (which would probably indicate that the change file is fouled up).
   while (true) {
      line↑;
      if (!input_ln(change_file)) return;
      if (limit < 2) continue;
      if (buffer[0] ≠ '@') continue;
      if (buffer[1] ≥ 'X' ∧ buffer[1] ≤ 'Z') buffer[1] += 'z' - 'Z';	// lowercasify
      if (buffer[1] ≡ 'x') break;
      if (buffer[1] ≡ 'y' ∨ buffer[1] ≡ 'z') loc ← 2, err_print("! Where is the matching @x?");
   }
// 12.7‡12.8: Skip to the next nonblank line; ≪return≫ if end of file
// Here we are looking at lines following the ‹@x›.
   do {
      line↑;
      if (!input_ln(change_file)) {
         err_print("! Change file ended after @x");
         return;
      }
   } while (limit ≤ 0);
// 12.8‡
   SwapBuffers(); // Move ≪buffer≫ and ≪limit≫ to ≪change_buffer≫ and ≪change_limit≫
}

// 12.6‡12.9: Move ≪buffer≫ and ≪limit≫ to ≪change_buffer≫ and ≪change_limit≫
// Editor's Note:
// ∙	This was orginally a multiply-used module.
inline void SwapBuffers(void) {
   change_limit ← limit;
   if (limit > 0) for (enum {0..buf_size} k ∈ limit) change_buffer[k] ← buffer[k];
}

// 12.9‡12.10:
// The following procedure is used to see if the next change entry should go into effect; it is called only when ≪changing≫ is false.
// The idea is to test whether or not the current contents of ≪buffer≫ matches the current contents of ≪change_buffer≫.
// If not, there's nothing more to do; but if so, a change is called for:
// All of the text down to the ‹@y› is supposed to match.
// An error message is issued if any discrepancy is found.
// Then the procedure prepares to read the next line from ≪change_file≫.
void check_change(void) {	// switches to ≪change_file≫ if the buffers match
   if (lines_dont_match()) return;
   integer n ← 0;	// the number of discrepancies found
   while (true) {
      change_changing();	// now it's ≪true≫
      line↑;
      if (!input_ln(change_file)) {
         err_print("! Change file ended before @y");
         change_limit ← 0, change_changing();	// ≪false≫ again
         return;
      }
   // ‡12.11: If the current line starts with ‹@y›, report any discrepancies and ≪return≫
      if (limit > 1 ∧ buffer[0] ≡ '@') {
         if (buffer[1] ≥ 'X' ∧ buffer[1] ≤ 'Z') buffer[1] += 'z' - 'Z';	// lowercasify
         if (buffer[1] ≡ 'x' ∨ buffer[1] ≡ 'z') loc ← 2, err_print("! Where is the matching @y?");
         else if (buffer[1] ≡ 'y') {
            if (n > 0) loc ← 2, err_print("! Hmm... %1d of the preceding lines failed to match", n);
            return;
         }
      }
   // 12.11‡
      SwapBuffers(); // Move ≪buffer≫ and ≪limit≫ to ≪change_buffer≫ and ≪change_limit≫
      change_changing();	// now it's ≪false≫
      line↑;
      if (!input_ln(web_file)) {
         err_print("! WEB file ended during a change");
         input_has_ended ← true; return;
      }
      if (lines_dont_match()) n↑;
   }
}
// 12.10‡12.13:
// The ≪get_line()≫ procedure is called when ≪loc > limit≫;
// it puts the next line of merged input into the buffer and updates the other variables appropriately. A space is placed at the right end of the line.
void get_line(void) {	// inputs the next line
   while (true) {
      if (changing) {
      // ‡12.15: Read from ≪change_file≫ and maybe turn off ≪changing≫
         line↑;
         if (!input_ln(change_file)) {
            err_print("! Change file ended without @z");
            buffer[0] ← '@', buffer[1] ← 'z', limit ← 2;
         }
         if (limit > 1 ∧ buffer[0] ≡ '@') { // check if the change has ended
            if (buffer[1] ≥ 'X' ∧ buffer[1] ≤ 'Z') buffer[1] += 'z' - 'Z';	// lowercasify
            if (buffer[1] ≡ 'x' ∨ buffer[1] ≡ 'y') loc ← 2, err_print("! Where is the matching @z?");
            else if (buffer[1] ≡ 'z') prime_the_change_buffer(), change_changing();
         }
      // 12.15‡
      }
      if (changing) break;
   // ‡12.14: Read from ≪web_file≫ and maybe turn on ≪changing≫
      line↑;
      if (!input_ln(web_file)) input_has_ended ← true;
      else if (limit ≡ change_limit ∧ buffer[0] ≡ change_buffer[0] ∧ change_limit > 0) check_change();
   // 12.14‡
      if (!changing) break;
   }
   loc ← 0, buffer[limit] ← ' ';
}
// 12.13‡12.17:
// Important milestones are reached during the input phase when certain control codes are sensed.

// Control codes in ‹WEB› begin with ‛‹@›’, and the next character identifies the code.
// Some of these are of interest only to ‹WEAVE›, so ‹TANGLE› ignores them;
// the others are converted by ‹TANGLE› into internal code numbers by the ≪control_code()≫ function below.
// The ordering of these internal code numbers has been chosen to simplify the program logic;
// larger numbers are given to the control codes that denote more significant milestones.
#define ignore		0x00	// control code of no interest to ‹TANGLE›
#define control_text	0x83	// control code for ‛‹@t›’, ‛‹@^›’, etc.
#define format		0x84	// control code for ‛‹@f›’
#define definition	0x85	// control code for ‛‹@d›’
#define begin_Pascal	0x86	// control code for ‛‹@p›’
#define module_name	0x87	// control code for ‛‹@<›’
#define new_module	0x88	// control code for ‛‹@ ›’ and ‛‹@*›’

eight_bits control_code(ASCII_code c) {	// convert ≪c≫ after ‹@›
   switch (c) {
      case '@': return '@';	// ‛quoted’ at sign
      case '\'': return octal;	// precedes octal constant
      case '"': return hex;	// precedes hexadecimal constant
      case '$': return check_sum;	// string pool check sum
      case ' ': case tab_mark: return new_module;	// beginning of a new module
      case '*':
         print("*%1d", module_count + 1);
         update_terminal();	// print a progress report
      return new_module;	// beginning of a new module
      case 'D': case 'd': return definition;	// macro definition
      case 'F': case 'f': return format;	// format definition
      case '{': return begin_comment;	// begin-comment delimiter
      case '}': return end_comment;	// end-comment delimiter
      case 'P': case 'p': return begin_Pascal;	// «Pas» text in unnamed module
      case 'T': case 't': case '^': case '.': case ':': return control_text;	// control text to be ignored
      case '&': return join;	// concatenate two tokens
      case '<': return module_name;	// beginning of a module name
      case '=': return verbatim;	// beginning of «Pas» verbatim mode
      case '\\': return force_line;	// force a new line in «Pas» output
      default: return ignore;	// ignore all other cases
   }
}

// 12.17‡12.18:
// The ≪skip_ahead()≫ procedure reads through the input at fairly high speed until finding the next non-ignorable control code, which it returns.
eight_bits skip_ahead(void) {	// skip to next control code
   while (true) {
      if (loc > limit) {
         get_line(); if (input_has_ended) break;
      }
      buffer[limit + 1] ← '@';
      while (buffer[loc] ≠ '@') loc↑;
      if (loc ≤ limit) {
         loc += 2;
         eight_bits c ← control_code(buffer[loc - 1]);	// control code found
         if (c ≠ ignore ∨ buffer[loc - 1] ≡ '>') return c;
      }
   }
   return new_module;
}

// 12.18‡12.19:
// The ≪skip_comment()≫ procedure reads through the input at somewhat high speed
// until finding the first unmatched right brace or until coming to the end of the file.
// It ignores characters following ‛‹\›’ characters, since all braces that aren't nested are supposed to be hidden in that way.
// For example, consider the process of skipping the first comment below,
// where the string containing the right brace has been typed as ‹`\.\}'› in the ‹WEB› file.
void skip_comment(void) {	// skips to next unmatched ‛‹}›’
   eight_bits bal ← 0;	// excess of left braces
   while (true) {
      if (loc > limit) {
         get_line();
         if (input_has_ended) {
            err_print("! Input ended in mid-comment");
            return;
         }
      }
      ASCII_code c ← buffer[loc↑];	// current character
   // ‡12.20: Do special things when ≪c ≡ '@', '\', '{', '}'≫; ≪return≫ at end
      if (c ≡ '@') {
         c ← buffer[loc];
         if (c ≠ ' ' ∧ c ≠ tab_mark ∧ c ≠ '*' ∧ c ≠ 'z' ∧ c ≠ 'Z') loc↑;
         else {
            err_print("! Section ended in mid-comment");
            loc↓; return;
         }
      } else if (c ≡ '\\' ∧ buffer[loc] ≠ '@') loc↑;
      else if (c ≡ '{') bal↑;
      else if (c ≡ '}') {
         if (bal ≡ 0) return;
         bal↓;
      }
   // 12.20‡
   }
}
// 12.19‡

// §13. Inputting the Next Token.
// ‡13.1: Globals in the outer block (23/28)
// As stated above, ‹TANGLE›'s most interesting input procedure is the ≪get_next()≫ routine that inputs the next token.
// However, the procedure isn't especially difficult.

// In most cases the tokens output by ≪get_next()≫ have the form used in replacement texts, except that two-byte tokens are not produced.
// An identifier that isn't one letter long is represented by the output ‛≪identifier≫’,
// and in such a case the global variables ≪id_first≫ and ≪id_loc≫ will have been set to the appropriate values needed by the ≪id_lookup()≫ procedure.
// A string that begins with a double-quote is also considered an ≪identifier≫,
// and in such a case the global variable ≪double_chars≫ will also have been set appropriately.
// Control codes produce the corresponding output of the ≪control_code()≫ function above;
// and if that code is ≪module_name≫, the value of ≪cur_module≫ will point to the ≪byte_start≫ entry for that module name.

// Another global variable, ≪scanning_hex≫, is ≪true≫ during the time that the letters ‹A› through ‹F› should be treated as if they were digits.
name_pointer cur_module;	// name of module just scanned
// ‡13.2: Set initial values (12/14)
boolean scanning_hex ← false;	// are we scanning a hexadecimal constant?
// 13.2‡
// 13.1‡13.3:
// At the top level, ≪get_next()≫ is a multi-way switch based on the next character in the input buffer.
// A ≪new_module≫ code is inserted at the very end of the input file.
eight_bits get_next(void) {	// produces the next input token
   while (true) {
      if (loc > limit) {
         get_line(); if (input_has_ended) break;
      }
      eight_bits c ← buffer[loc↑];	// the current character
      if (scanning_hex) {
      // ‡13.4: Return if ≪c≫ is a hexadecimal digit, otherwise set ≪scanning_hex ← false≫
         if (c ≥ '0' ∧ c ≤ '9' ∨ c ≥ 'A' ∧ c ≤ 'F') Return(c);
         scanning_hex ← false
      // 13.4‡
      }
      switch (c) {
         case 'A': case 'B': case 'C': case 'D': case 'E': case 'F': case 'G': case 'H': case 'I': case 'J': case 'K': case 'L': case 'M':
         case 'N': case 'O': case 'P': case 'Q': case 'R': case 'S': case 'T': case 'U': case 'V': case 'W': case 'X': case 'Y': case 'Z':
         case 'a': case 'b': case 'c': case 'd': case 'e': case 'f': case 'g': case 'h': case 'i': case 'j': case 'k': case 'l': case 'm':
         case 'n': case 'o': case 'p': case 'q': case 'r': case 's': case 't': case 'u': case 'v': case 'w': case 'x': case 'y': case 'z': {
         // ‡13.6: Get an identifier
         // We have to look at the preceding character to make sure this isn't part of a real constant,
         // before trying to find an identifier starting with ‛‹e›’ or ‛‹E›’.
            if ((c ≡ 'e' ∨ c ≡ 'E') ∧ loc > 1 ∧ buffer[loc - 2] ≤ '9' ∧ buffer[loc - 2] ≥ '0') Return('E');	// exponent of a real constant
            id_first ← ↓loc;
            for (eight_bits d; (d ← buffer[↑loc]) ≥ '0' ∧ (d ≤ '9' ∨ d ≥ 'A') ∧ (d ≤ 'Z' ∨ d ≥ 'a') ∧ d ≤ 'z' ∨ d ≡ '_'; );
            if (loc > id_first + 1) { id_loc ← loc; Return(identifier); }
         // 13.6‡
         }
         Return(c);
         case '"':
         // ‡13.7: Get a preprocessed string
         // A string that starts and ends with double-quote marks is converted into an identifier
         // that behaves like a numeric macro by means of the following piece of the program.
            double_chars ← 0, id_first ← loc - 1;
            do {
               eight_bits d ← buffer[loc↑];	// the next character
               if (d ≡ '"' ∨ d ≡ '@') {
                  if (buffer[loc] ≡ d) loc↑, d ← 0, double_chars↑;
                  else if (d ≡ '@') err_print("! Double @ sign missing");
               } else if (loc > limit) err_print("! String constant didn't end"), d ← '"';
            } while (d ≠ '"');
            id_loc ← loc - 1
         // 13.7‡
         Return(identifier);
         case '@':
         // ‡13.8: Get control code and possible module name
         // After an ‹@› sign has been scanned, the next character tells us whether there is more work to do.
            c ← control_code(buffer[loc↑]);
            if (c ≡ ignore) continue;
            else if (c ≡ hex) scanning_hex ← true;
            else if (c ≡ module_name) {
            // ‡13.9: Scan the module name and make ≪cur_module≫ point to it
            // ‡13.11: Put module name into ≪mod_text[1..k]≫
               enum {0..longest_name} k ← 0;	// index into ≪mod_text≫
               while (true) {
                  if (loc > limit) {
                     get_line();
                     if (input_has_ended) {
                        err_print("! Input ended in section name");
                        break;
                     }
                  }
                  eight_bits d ← buffer[loc];	// the next character
               // ‡13.12: If end of name, ≪break≫
                  if (d ≡ '@') {
                     d ← buffer[loc + 1];
                     if (d ≡ '>') { loc += 2; break; }
                     if (d ≡ ' ' ∨ d ≡ tab_mark ∨ d ≡ '*') {
                        err_print("! Section name didn't end"); break;
                     }
                     mod_text[↑k] ← '@', loc↑;	// now ≪d ≡ buffer[loc]≫ again
                  }
               // 13.12‡
                  loc↑; if (k < longest_name - 1) k↑;
                  if (d ≡ ' ' ∨ d ≡ tab_mark) {
                     d ← ' '; if (mod_text[k - 1] ≡ ' ') k↓;
                  }
                  mod_text[k] ← d;
               }
            // ‡13.13: Check for overlong name
               if (k ≥ longest_name - 2) {
                  print("\n! Section name too long: ");
                  for (enum {0..longest_name} j ← 1 ⋯ 25) print(xchr[mod_text[j]]);
                  print("..."), mark_harmless();
               }
            // 13.13‡
               if (mod_text[k] ≡ ' ' ∧ k > 0) k↓;
            // 13.11‡
               if (k > 3) cur_module ← mod_text[k] ≡ '.' ∧ mod_text[k - 1] ≡ '.' ∧ mod_text[k - 2] ≡ '.'? prefix_lookup(k - 3): mod_lookup(k);
               else cur_module ← mod_lookup(k);
            // 13.9‡
            } else if (c ≡ control_text) {
               do c ← skip_ahead(); while (c ≡ '@');
               if (buffer[loc - 1] ≠ '>') err_print("! Improper @ within control text");
               continue;
            }
         // 13.8‡13.5: Compress two-symbol combinations like ‛‹:=›’
         // Note that the following code substitutes ‹@{› and ‹@}› for the respective combinations ‛‹(*›’ and ‛‹*)›’.
         // Explicit braces should be used for «TeX» comments in «Pas» text.
#define compress(A) { if (loc ≤ limit) { loc↑; Return(A); } }
            case '.': switch (buffer[loc]) {
               case '.': compress(double_dot); break;
               case ')': compress(']'); break;
            }
            break;
            case ':': switch (buffer[loc]) {
               case '=': compress(left_arrow); break;
            }
            break;
            case '=': switch (buffer[loc]) {
               case '=': compress(equivalence_sign); break;
            }
            break;
            case '>': switch (buffer[loc]) {
               case '=': compress(greater_or_equal); break;
            }
            break;
            case '<': switch (buffer[loc]) {
               case '=': compress(less_or_equal); break;
               case '>': compress(not_equal); break;
            }
            break;
            case '(': switch (buffer[loc]) {
               case '*': compress(begin_comment); break;
               case '.': compress('['); break;
            }
            break;
            case '*': switch (buffer[loc]) {
               case ')': compress(end_comment); break;
            }
            break;
#undef compress
         // 13.5‡
         Return(c);
         case ' ': case tab_mark: break;	// ignore spaces and tabs
         case '{': skip_comment(); break;
         case '}': err_print("! Extra }"); break;
   //	↔	Extra }
         default:
            if (c < 0x80) Return(c);
         break; // ignore nonstandard characters
      }
   }
   Return(new_module);
}
// 13.3‡

// §14. Scanning a Numeric Definition.
// ‡14.1: Globals in the outer block (24/28)
// When ‹TANGLE› looks at the «Pas» text following the ‛‹=›’ of a numeric macro definition,
// it calls on the precedure ≪scan_numeric(p)≫, where ≪p≫ points to the name that is to be defined.
// This procedure evaluates the right-hand side,
// which must consist entirely of integer constants and defined numeric macros connected with ‹+› and ‹-› signs (no parentheses).
// It also sets the global variable ≪next_control≫ to the control code that terminated this definition.

// A definition ends with the control codes ≪definition≫, ≪format≫, ≪module_name≫, ≪begin_Pascal≫, and ≪new_module≫,
// all of which can be recognized by the fact that they are the largest values ≪get_next()≫ can return.
#define end_of_definition(A) (A ≥ format)	// is ≪#≫ a control code ending a definition?

eight_bits next_control;	// control code waiting to be acted upon

// 14.1‡14.2:
// The evaluation of a numeric expression makes use of two variables called the ≪accumulator≫ and the ≪next_sign≫.
// At the beginning, ≪accumulator≫ is zero and ≪next_sign≫ is $+1$.
// When a ‹+› or ‹-› is scanned, ≪next_sign≫ is multiplied by the value of that sign.
// When a numeric value is scanned, it is multiplied by ≪next_sign≫ and added to the ≪accumulator≫, then ≪next_sign≫ is reset to $+1$.
#define add_in(A) ≡ accumulator += next_sign*(A), next_sign ← +1;

void scan_numeric(name_pointer p) {	// defines numeric macros
// ‡14.3: Set ≪accumulator≫ to the value of the right-hand side
   integer accumulator ← 0;	// accumulates sums
   enum {-1..+1} next_sign ← +1;	// sign to attach to next value
   while (true) {
      next_control ← get_next();
   reswitch:
      switch (next_control) {
         case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9': {
         // ‡14.5: Set ≪val≫ to value of decimal constant, and set ≪next_control≫ to the following token
            integer val ← 0;	// constants being evaluated
            do val ← 10*val + next_control - '0', next_control ← get_next(); while (next_control ≤ '9' ∧ next_control ≥ '0')
         // 14.5‡
            add_in(val);
         }
         goto reswitch;
         case octal: {
         // ‡14.6: Set ≪val≫ to value of octal constant, and set ≪next_control≫ to the following token
            integer val ← 0;	// constants being evaluated
            next_control ← '0';
            do val ← 010*val + next_control - '0', next_control ← get_next(); while (next_control ≤ '7' ∧ next_control ≥ '0')
         // 14.6‡
            add_in(val);
         }
         goto reswitch;
         case hex: {
         // ‡14.7: Set ≪val≫ to value of hexadecimal constant, and set ≪next_control≫ to the following token
            integer val ← 0;	// constants being evaluated
            next_control ← '0';
            do {
               if (next_control ≥ 'A') next_control += '0' + 10 - 'A';
               val ← 0x10*val + next_control - '0', next_control ← get_next();
            } while (next_control ≤ 'F' ∧ next_control ≥ '0' ∧ (next_control ≤ '9' ∨ next_control ≥ 'A'))
         // 14.7‡
            add_in(val);
         }
         goto reswitch;
         case identifier: {
            name_pointer q ← id_lookup(normal);	// points to identifiers being evaluated
            if (ilk[q] ≠ numeric) {
               next_control ← '*'; goto reswitch;	// leads to error
            }
            add_in(equiv[q] - 0x8000);
         }
         break;
         case '+': break;
         case '-': next_sign ← -next_sign; break;
         case format: case definition: case module_name: case begin_Pascal: case new_module: goto done;
         case ';': err_print("! Omit semicolon in numeric definition"); break;
         default:
         // ‡14.4: Signal error, flush rest of the definition
            err_print("! Improper numeric definition will be flushed");
            do next_control ← skip_ahead(); while (!end_of_definition(next_control));
            if (next_control ≡ module_name)	// we want to scan the module name too
               loc -= 2, next_control ← get_next();
            accumulator ← 0;
         // 14.4‡
         goto done;
      }
   }
done:
// 14.3‡
   if (abs(accumulator) ≥ 0x8000) err_print("! Value too big: %1d", accumulator), accumulator ← 0;
   equiv[p] ← accumulator + 0x8000;	// name ≪p≫ now is defined to equal ≪accumulator≫
}
// 14.2‡

// §15. Scanning a Macro Definition.
// ‡15.1:
// The rules for generating the replacement texts corresponding to simple macros,
// parametric macros, and «Pas» texts of a module are almost identical, so a single procedure is used for all three cases.
// The differences are that
// a)	The sign ≪#≫ denotes a parameter only when it appears outside of strings in a parametric macro; otherwise it stands for the ASCII character ≪#≫.
//	(This is not used in standard «Pas», but some «Pas» s allow, for example, ‛‹/#›’ after a certain kind of file name.)
// b)	Module names are not allowed in simple macros or parametric macros;
//	in fact, the appearance of a module name terminates such macros and denotes the name of the current module.
// c)	The symbols ‹@d› and ‹@f› and ‹@p› are not allowed after module names, while they terminate macro definitions.

// 15.1‡15.2: Globals in the outer block (25/28)
// Therefore there is a procedure ≪scan_repl()≫ whose parameter ≪t≫ specifies either ≪simple≫ or ≪parametric≫ or ≪module_name≫.
// After ≪scan_repl()≫ has acted, ≪cur_repl_text≫ will point to the replacement text just generated,
// and ≪next_control≫ will contain the control code that terminated the activity.
text_pointer cur_repl_text;	// replacement text formed by ≪scan_repl()≫

// 15.2‡15.3:
void scan_repl(eight_bits t) {	// creates a replacement text
   eight_bits bal ← 0;	// left parentheses minus right parentheses
   sixteen_bits a;	// the current token
   while (true) {
      a ← get_next();
      switch (a) {
         case '(': bal↑; break;
         case ')':
            if (bal ≡ 0) err_print("! Extra )");
            else bal↓;
         break;
         case '\'':
         // ‡15.6: Copy a string from the buffer to ≪tok_mem[]≫
            ASCII_code b ← '\'';	// a character from the buffer
            while (true) {
               app_repl(b);
               if (b ≡ '@')
                  if (buffer[loc] ≡ '@') loc↑;	// store only one ‹@›
                  else err_print("! You should double @ signs in strings");
               if (loc ≡ limit) err_print("! String didn't end"), buffer[loc] ← '\'', buffer[loc + 1] ← 0;
               b ← buffer[loc↑];
               if (b ≡ '\'') {
                  if (buffer[loc] ≠ '\'') break;
                  else loc↑, app_repl('\'');
               }
            }
         // now ≪a≫ holds the final ≪'\''≫ that will be stored
         // 15.6‡
         break;
         case '#':
            if (t ≡ parametric) a ← param;
         // ‡15.5: In cases that ≪a≫ is a non-ASCII token (≪identifier≫, ≪module_name≫, etc.),
         // either process it and change ≪a≫ to a byte that should be stored, or ≪continue;≫ if ≪a≫ should be ignored,
         // or ≪goto done≫ if ≪a≫ signals the end of this replacement text
            case identifier: a ← id_lookup(normal), app_repl(a/0x100 + 0x80), a %= 0x100; break;
            case module_name:
               if (t ≠ module_name) goto done;
               else app_repl(cur_module/0x100 + 0xa8), a ← cur_module%0x100;
            break;
            case verbatim:
            // ‡15.7: Copy verbatim string from the buffer to ≪tok_mem[]≫
               app_repl(verbatim);
               buffer[limit + 1] ← '@';
               while (true)
                  if (buffer[loc] ≠ '@') app_repl(buffer[loc↑]);
                  else if (loc < limit ∧ buffer[loc + 1] ≡ '@') app_repl('@'), loc += 2;
                  else break;
               if (loc ≥ limit) err_print("! Verbatim string didn't end");
               else if (buffer[loc + 1] ≠ '>') err_print("! You should double @ signs in verbatim strings");
               loc += 2;
            // another ≪verbatim≫ byte will be stored, since ≪a ≡ verbatim≫
            // 15.7‡
            break;
            case definition: case format: case begin_Pascal:
               if (t ≠ module_name) goto done;
               else {
                  err_print("! @%c is ignored in Pascal text", xchr[buffer[loc - 1]]); continue;
               }
            break;
            case new_module: goto done;
         // 15.5‡
         break;
         default: break;
      }
      app_repl(a);	// store ≪a≫ in ≪tok_mem[]≫
   }
done:
   next_control ← a;
// ‡15.4: Make sure the parentheses balance
   if (bal ≡ 1) err_print("! Missing )"); else if (bal > 1) err_print("! Missing %1d )'s", bal);
   while (bal > 0) app_repl(')'), bal↓;
// 15.4‡
   if (text_ptr > max_texts - zz) overflow("text");
   cur_repl_text ← text_ptr, tok_start[text_ptr↑ + zz] ← tok_ptr[z];
   if (z ≡ zz - 1) z ← 0; else z↑;
}

// 15.3‡15.8:
// The following procedure is used to define a simple or parametric macro, just after the ‛‹==›’ of its definition has been scanned.
void define_macro(eight_bits t) {
   name_pointer p ← id_lookup(t);	// the identifier being defined
   scan_repl(t);
   equiv[p] ← cur_repl_text, text_link[cur_repl_text] ← 0;
}
// 15.8‡

// §16. Scanning a Module.
// ‡16.1: Globals in the outer block (26/28)
// The ≪scan_module()≫ procedure starts when ‛‹@ ›’ or ‛‹@*›’ has been sensed in the input, and it proceeds until the end of that module.
// It uses ≪module_count≫ to keep track of the current module number; with luck, ‹WEAVE› and ‹TANGLE› will both assign the same numbers to modules.
enum {0x3000} module_count;	// the current module number

// 16.1‡16.2:
// The top level of ≪scan_module()≫ is trivial.
void scan_module(void) {
   module_count↑;
// ‡16.3: Scan the definition part of the current module
   next_control ← 0;
   while (true) {
      while (next_control ≤ format) {
         next_control ← skip_ahead();
         if (next_control ≡ module_name)	// we want to scan the module name too
            loc -= 2, next_control ← get_next();
      }
      if (next_control ≠ definition) break;
      next_control ← get_next();	// get identifier name
      if (next_control ≠ identifier) {
         err_print("! Definition flushed, must start with ", "identifier of length > 1"); continue;
      }
      next_control ← get_next();	// get token after the identifier
      if (next_control ≡ '=') {
         scan_numeric(id_lookup(numeric)); continue;
      } else if (next_control ≡ equivalence_sign) {
         define_macro(simple); continue;
      } else {
      // ‡16.4: If the next text is ‛≪(#)==≫’, call ≪define_macro()≫ and ≪continue≫
         if (next_control ≡ '(' ∧ (next_control ← get_next()) ≡ '#' ∧ (next_control ← get_next()) ≡ ')') {
            next_control ← get_next();
            if (next_control ≡ '=') err_print("! Use ≡ for macros"), next_control ← equivalence_sign;
            if (next_control ≡ equivalence_sign) { define_macro(parametric); continue; }
         }
      // 16.4‡
      }
      err_print("! Definition flushed since it starts badly");
   }
// 16.3‡16.5: Scan the «Pas» part of the current module
   name_pointer p;	// module name for the current module
   switch (next_control) {
      case begin_Pascal: p ← 0; break;
      case module_name:
         p ← cur_module;
      // ‡16.6: Check that ≪=≫ or ≪==≫ follows this module name, otherwise ≪return≫
         do next_control ← get_next(); while (next_control ≡ '+');	// allow optional ‛‹+=›’
         if (next_control ≠ '=' ∧ next_control ≠ equivalence_sign) {
            err_print("! Pascal text flushed, = sign is missing");
            do next_control ← skip_ahead(); while (next_control ≠ new_module);
            return;
         }
      // 16.6‡
      break;
      default: return;
   }
// ‡16.7: Insert the module number into ≪tok_mem[]≫
   store_two_bytes(0xd000 + module_count);	// ≪0xd000 ≡ 0xd0*0x100≫
// 16.7‡
   scan_repl(module_name);	// now ≪cur_repl_text≫ points to the replacement text
// ‡16.8: Update the data structure so that the replacement text is accessible
   if (p ≡ 0)	// unnamed module
      last_unnamed ← text_link[last_unnamed] ← cur_repl_text;
   else if (equiv[p] ≡ 0) equiv[p] ← cur_repl_text;	// first module of this name
   else {
      p ← equiv[p];
      while (text_link[p] < module_flag) p ← text_link[p];	// find end of list
      text_link[p] ← cur_repl_text;
   }
   text_link[cur_repl_text] ← module_flag;	// mark this replacement text as a nonmacro
// 16.8‡
// 16.5‡
}
// 16.2‡

// §17. Debugging.
// ‡17.1: Globals in the outer block (27/28)
// The «Pas» debugger with which ‹TANGLE› was developed allows breakpoints to be set,
// and variables can be read and changed, but procedures cannot be executed.
// Therefore a ‛≪debug_help()≫’ procedure has been inserted in the main loops of each phase of the program;
// when ≪ddt≫ and ≪dd≫ are set to appropriate values, symbolic printouts of various tables will appear.

// The idea is to set a breakpoint inside the ≪debug_help()≫ routine, at the place of ‛‹ignorespaces›≪breakpoint:≫‹unskip›’ below.
// Then when ≪debug_help()≫ is to be activated, set ≪trouble_shooting≫ equal to ≪true≫.
// The ≪debug_help()≫ routine will prompt you for values of ≪ddt≫ and ≪dd≫,
// discontinuing this when ≪ddt ≤ 0≫; thus you type $2n + 1$ integers, ending with zero or a negative number.
// Then control either passes to the breakpoint, allowing you to look at and/or change variables (if you typed zero),
// or to exit the routine (if you typed a negative value).

// Another global variable, ≪debug_cycle≫, can be used to skip silently past calls on ≪debug_help()≫.
// If you set ≪debug_cycle > 1≫, the program stops only every ≪debug_cycle≫ times ≪debug_help()≫ is called;
// however, any error stop will set ≪debug_cycle≫ to zero.
#if DEBUG
// ‡17.2: Set initial values (14/14)
boolean trouble_shooting ← true;	// is ≪debug_help()≫ wanted?
// 17.2‡
integer ddt;			// operation code for the ≪debug_help()≫ routine
integer dd;			// operand in procedures performed by ≪debug_help()≫
// ‡17.2: Set initial values (14/14) [continued]
integer debug_cycle ← 1;		// threshold for ≪debug_help()≫ stopping
integer debug_skipped ← 0;		// we have skipped this many ≪debug_help()≫ calls
// 17.2‡
// trouble_shooting ← false, debug_cycle ← 99999;	// use these when it almost works
text_file term_in;		// the user's terminal as an input file
#endif // DEBUG

// 17.1‡17.3:
// (#) system dependencies
#if DEBUG
void debug_help(void) {	// routine to display various things
   if (↑debug_skipped < debug_cycle) return;
   debug_skipped ← 0;
   while (true) {
      print("\n#"), update_terminal();	// prompt
      read(term_in, ddt);	// read a debug-command code
      if (ddt < 0) return;
      else if (ddt ≡ 0) {
         goto breakpoint;	// go to every label at least once
      breakpoint:
         ddt ← 0;
      } else {
         read(term_in, dd);
         switch (ddt) {
            case 1: print_id(dd); break;
            case 2: print_repl(dd); break;
            case 3:
               for (integer k ← 1 ⋯ dd) print(xchr[buffer[k]]);
            break;
            case 4:
               for (integer k ← 1 ⋯ dd) print(xchr[mod_text[k]]);
            break;
            case 5:
               for (integer k ← 1 ⋯ out_ptr) print(xchr[out_buf[k]]);
            break;
            case 6:
               for (integer k ← 1 ⋯ dd) print(xchr[out_contrib[k]]);
            break;
            default: print("?"); break;
         }
      }
   }
}
#endif // DEBUG
// 17.3‡

// §18. The Main Program.
// ‡18.1:
// We have defined plenty of procedures, and it is time to put the last pieces of the puzzle in place.
// Here is where ‹TANGLE› starts, and where it ends.
// (#) system dependencies
int main(void) {
// ‡1.2: [continued]
// ‡2.8: Set initial values (4/14)
// The following system-independent code makes the ≪xord≫ array contain a suitable inverse to the information in ≪xchr≫.
   for (i ← first_text_char ⋯ last_text_char) xord[chr(i)] ← ' ';
   for (i ← 0x01 ⋯ 0xff) xord[xchr[i]] ← i;
   xord[' '] ← ' ';
// 2.8‡3.3: Set initial values (5/14)
// Different systems have different ways of specifying that the output on a certain file will appear on the user's terminal.
// Here is one way to do this on the «Pas» system that was used in ‹TANGLE›'s initial development:
// (#) system dependencies
   rewrite(term_out, "TTY:");	// send ≪term_out≫ output to the terminal
// 3.3‡3.8: Set initial values (6/14)
// The following code opens ≪Pascal_file≫ and ≪pool≫.
// Since these files were listed in the program header,
// we assume that the «Pas» runtime system has checked that suitable external file names have been given.
// (#) system dependencies
   rewrite(Pascal_file), rewrite(pool);
// 3.8‡17.2: Set initial values (14/14) [continued]
// The debugging routine needs to read from the user's terminal.
// (#) system dependencies
#if DEBUG
   reset(term_in, "TTY:", "/I");	// open ≪term_in≫ as the terminal, don't do a ≪get≫
#endif // DEBUG
// 17.2‡
// 1.2‡12.12: Initialize the input system
   open_input(), line ← 0, other_line ← 0;
   changing ← true, prime_the_change_buffer(), change_changing();
   limit ← 0, loc ← 1, buffer[0] ← ' ', input_has_ended ← false;
// 12.12‡
   print(banner "\n");	// print a ‟banner line”
// ‡18.2: Phase I: Read all the user's text and compress it into ≪tok_mem[]≫
   phase_one ← true;
   module_count ← 0;
   do next_control ← skip_ahead(); while (next_control ≠ new_module);
   while (!input_has_ended) scan_module();
// ‡12.16: Check that all changes have been read
// At the end of the program, we will tell the user if the change file had a line that didn't match any relevant line in ≪web_file≫.
   if (change_limit ≠ 0) {	// ≪changing≫ is false
      for (ii ← 0 ⋯ change_limit) buffer[ii] ← change_buffer[ii];
      limit ← change_limit, changing ← true, line ← other_line, loc ← change_limit;
      err_print("! Change file entry did not match");
   }
// 12.16‡
   phase_one ← false;
// 18.2‡
#if STATS
   for (ii ← 0 ⋯ zz - 1) max_tok_ptr[ii] ← tok_ptr[ii];
#endif // STATS
// ‡11.1: Phase II: Output the contents of the compressed tables
// To complete the output process, we need a routine that takes the results of ≪get_output()≫
// and feeds them to ≪send_out()≫, ≪send_val()≫, or ≪send_sign()≫.
// This procedure ‛≪send_the_output()≫’ will be invoked just once, as follows:
   if (text_link[0] ≡ 0) print("\n! No output was specified."), mark_harmless();
   else {
      print("\nWriting the output file"), update_terminal();
   // ‡9.7: Initialize the output stacks
   // To get the output process started, we will perform the following initialization steps.
   // We may assume that ≪text_link[0]≫ is nonzero, since it points to the «Pas» text in the first unnamed module that generates code;
   // if there are no such modules, there is nothing to output, and an error message will have been generated before we do any of the initialization.
      stack_ptr ← 1, brace_level ← 0, cur_name ← 0, cur_repl ← text_link[0];
      zo ← cur_repl%zz, cur_byte ← tok_start[cur_repl], cur_end ← tok_start[cur_repl + zz], cur_mod ← 0;
   // 9.7‡10.3: Initialize the output buffer
   // During the output process, ≪line≫ will equal the number of the next line to be output.
      out_state ← misc, out_ptr ← 0, break_ptr ← 0, semi_ptr ← 0, out_buf[0] ← 0, line ← 1;
   // 10.3‡
      send_the_output();
   // ‡10.5: Empty the last line from the buffer
      break_ptr ← out_ptr, semi_ptr ← 0, flush_buffer();
      if (brace_level ≠ 0) err_print("! Program ended at brace level %1d", brace_level);
   // 10.5‡
      print("\nDone.");
   }
// 11.1‡
end_of_TANGLE: // go here to finish
   if (string_ptr > 0x100) {
   // ‡18.3: Finish off the string pool file
      print("\n%1d strings written to string pool file.", string_ptr - 0x100);
      write(pool, "*");
      for (ii ← 1 ⋯ 9) out_buf[ii] ← pool_check_sum%10, pool_check_sum /= 10;
      for (ii ← 9 ↓ 1) write(pool, "%c", xchr['0' + out_buf[ii]]);
      write(pool, "\n");
   // 18.3‡
   }
#if STATS
// ‡18.5: Print statistics about memory usage
   print("\nMemory usage statistics:");
   print("\n%1d names, %1d replacement texts;", name_ptr, text_ptr);
   print("\n%1d", byte_ptr[0]);
// ‡18.4: Globals in the outer block (28/28)
// Editor's Note
// ∙	Localized to the for loop where it is used.
   for (enum {ww} wo ← 1 ⋯ ww - 1) print("+%1d", byte_ptr[wo]);
// 18.4‡
   if (phase_one) for (ii ∈ zz) max_tok_ptr[ii] ← tok_ptr[ii];
   print(" bytes, %1d", max_tok_ptr[0]);
   for (ii ← 1 ⋯ zz - 1) print("+%1d", max_tok_ptr[ii]);
   print(" tokens.");
// 18.5‡
#endif // STATS
// here files should be closed if the operating system requires it
// ‡18.6: Print the job ≪history≫
// Some implementations may wish to pass the ≪history≫ value to the operating system
// so that it can be used to govern whether or not other programs are started. Here we simply report the history to the user.
// (#) system dependencies
   switch (history) {
      case spotless: print("\n(No errors were found.)"); break;
      case harmless_message: print("\n(Did you see the warning message above?)"); break;
      case error_message: print("\n(Pardon me, but I think I spotted something wrong.)"); break;
      case fatal_message: print("\n(That was a fatal error, my friend.)"); break;
   } // there are no other cases
// 18.6‡
}
// 18.1‡

// §19. System-Dependent Changes.
// ‡19.1:
// This module should be replaced, if necessary, by changes to the program that are necessary to make ‹TANGLE› work at a particular installation.
// It is usually best to design your change file so that all changes to previous modules preserve the module numbering;
// then everybody's version will be consistent with the printed program.
// More extensive changes, which introduce new modules, can be inserted here; then only the index itself will get a new module number.
// (#) system dependencies
// 19.1‡

// §20. Index.
// ‡20.1:
// Here is a cross-reference table for the ‹TANGLE› processor.
// All modules in which an identifier is used are listed with that identifier,
// except that reserved words are indexed only when they appear in format definitions,
// and the appearances of identifiers in module names are not indexed.
// Underlined entries correspond to where the identifier was declared. Error messages and a few other things like ‟ASCII code” are indexed here too.
// 20.1‡
