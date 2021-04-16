// This program by D. E. Knuth is not copyrighted and can be used freely.
// Version 4.5, 2002/12.
#include <stdio.h>
#include <stdlib.h>
#include <setjmp.h>
#include <stdarg.h>

// §19. System-Dependent Changes.
// This module should be replaced, if necessary, by changes to the program that are necessary to make ‹TANGLE› work at a particular installation.
// It is usually best to design your change file so that all changes to previous modules preserve the module numbering;
// then everybody's version will be consistent with the printed program.
// More extensive changes, which introduce new modules, can be inserted here; then only the index itself will get a new module number.

// §20. Index.
// Not needed or used for on-line text, since items may be found by search.

// §1. Introduction.
// This program converts a ‹WEB› file to a «Pas» file.
// Since this program describes itself, a bootstrapping process is needed to get started: either compling with an earlier version or by hand.

// The ‟banner line” defined here should be changed whenever ‹TANGLE› is modified.
#define Banner "This is TANGLE, Version 4.5"

// The directives originally used were for:
// ∙	no range check,
// ∙	catch arithmetic overflow,
// ∙	no debug overhead.

// Generic labels are used for:
// ∙	‛ReSwitch:’	for the top of a «·switch·» statement that is being used as a finite-state control
// ∙	‛Continue:’	for a «·continue·» two or more levels up
// ∙	‛Break:’	for a «·break·» two or more levels up

// The following parameters, suitable for  «TeX», should therefore also be enough for most applications of ‹TANGLE›.
#define InBufN 0x80	// Input lines should be ≤ InBufN in length.
#define StrMax 0x20000	// The number of bytes in identifiers, strings, and module names; previously required ≤ 0x10000.
#define TokMax 0x30000	// The number of bytes in compressed «Pas» code; previously required ≤ 0x10000.
#define NameN 0x1000	// The number of identifiers, strings, module names; must be ≤ 0x2800.
#define TextN 0x800	// The number of replacement texts, must be ≤ 0x2800.
#define HashN 353	// Should be prime.
#define NameMax 0x200	// Module names should be ≤ NameMax in length.
#define LineN 0x80	// Lines of «Pas» output have ≤ LineN characters.
#define ExBufN 0x100	// The length of output buffer, should be 2×LineN.
#define StackN 0x40	// The number of simultaneous levels of macro expansion.
#define IdMax 0x10	// Long identifiers are chopped to a length IdMax ≤ LineN.
#define ChopN 7		// Identifiers chopped to a length ≤ ChopN must be unique ― more strict than «Pas»'s 8, but this can be varied.

// Status, used to convey the result returned to the host OS, will contain one of four values at the end of every run:
typedef enum {
   Okayed = 0,	// For normal jobs.
   Warned = 1,	// A message of possible interest was printed but no serious errors were detected.
   Failed = 2,	// At least one error was found;
   Killed = 3	// The program stopped early and abnormally.
} ErrLevel;
ErrLevel Status = Okayed;	// How bad was this run?

// §2. The Character Set.
// Characters are treated internally by ‹WEAVE› and ‹TANGLE› as 8-bit bytes that provide an enhanced version of ASCII.
// The internal code is what ‹WEB› uses for preprocessed one-character constants like ‹'›.
typedef unsigned char InChar;	// 8-bit numbers, a subrange of the integers.

// Characters are treated externally as whatever the host system provides for and uses in text files.
// The following definitions should be adjusted if necessary.
#define ExCharLo 0x00	// The ordinal number of the smallest element of ExChar.
#define ExCharHi 0xff	// The ordinal number of the largest element of ExChar.
typedef char ExChar;	// typedef enum {ExCharLo..ExCharHi} ExChar.
typedef FILE *TextFile;	// typedef file(ExChar) TextFile;

InChar ByteOf[ExChar];		// Convert ExChar ⇒ InChar.

// Special codes below 0x20 used and named in ‹WEAVE› and ‹TANGLE›:
// ∙	The codes '\t', '\n', '\f' and '\r' are being used respectively for 0x09, 0x0a, 0x0c and 0x0d.
// ∙	Only '\t' is actually used in ‹TANGLE›.
#define AndL	0x04	// Equivalent to ‛‹∧›’.
#define NotL	0x05	// Equivalent to ‛‹¬›’.
#define InL	0x06	// Equivalent to ‛‹∈›’.
#define AssL	0x18	// Equivalent to ‛‹←›’.
#define NeL	0x1a	// Equivalent to ‛‹≠›’.
#define LeL	0x1c	// Equivalent to ‛‹≤›’.
#define GeL	0x1d	// Equivalent to ‛‹≥›’.
#define DefL	0x1e	// Equivalent to ‛‹≡›’.
#define OrL	0x1f	// Equivalent to ‛‹∨›’.

// The initialization of CharOf, like 'A' to CharOf[0x41] are compiled by «Pas» with 'A' as external.
// So this initialization will work correctly.
// If you have an extended set of characters that are easily incorporated into text files, you can assign codes arbitrarily here,
// giving an CharOf[] equivalent to whatever characters the users of ‹WEB› are allowed to have in their input files,
// provided that unsuitable characters do not correspond to special codes like '\r' that are listed above.
ExChar CharOf[InChar] = {	// Convert InChar ⇒ ExChar. The ASCII codes for 0x00-0x1f, 0x7f-0xff are not used.
   "        "  "        "	// 00-0f
   "        "  "        "	// 10-1f
   " !\"#$%&'" "()*+,-./"	// 20-2f
   "01234567"  "89:;<=>?"	// 30-3f
   "@ABCDEFG"  "HIJKLMNO"	// 40-4f
   "PQRSTUVW"  "XYZ[\\]^_"	// 50-5f
   "`abcdefg"  "hijklmno"	// 60-6f
   "pqrstuvw"  "xyz{|}~ "	// 70-7f
   "        "  "        "	// 80-8f
   "        "  "        "	// 90-9f
   "        "  "        "	// a0-af
   "        "  "        "	// b0-bf
   "        "  "        "	// c0-cf
   "        "  "        "	// d0-df
   "        "  "        "	// e0-ef
   "        "  "        "	// f0-ff
};

// §3. Input and Output.
// ‹TANGLE› and ‹WEAVE› use the same input conventions as «TeX», but on a much smaller scale.

// For interactive output of ExChar strings:
#define PutS(S)	fputs((S), stdout)
// Empty the terminal output buffer, to synchronize interactive output.
#define FlushEx() fflush(stdout)

// The main input comes from WebF; this input may be overridden by changes in DelF, if DelF ≠ NULL.
TextFile WebF, DelF;
// Check for and open the input files WebF and DelF and prepare them for reading.
void OpenInput(void) { reset(WebF, WebFile), reset(DelF, DelFile); }

// The main output goes to PasF, and string pool constants are written to StrF.
TextFile PasF, StrF;
// Check for and open the output files PasF and StrF.
void OpenOutput(void) { rewrite(PasF, PasFile), rewrite(StrF, StrFile); }

// The input buffer.
typedef enum {0..InBufN} InBufIx;
InChar InBuf[InBufIx];

// Buffer the next line of input from the file InF into InBuf[] and return an indication of the end of file.
// The line consists of InChar's from InBuf..InEnd-1; trailing blanks are ignored; none of the InChar's may be '\0', '\n', '\f', '\r' or 0x7f.
// The length of the line is InEnd - InBuf ≤ InBufN.
bool ReadLine(TextFile InF) {	// Input a line or return false.
   String InLast = InEnd = InBuf;	// InEnd without trailing blanks.
   if (NextCh(InF) ≡ EOF) return false;
   while (NextCh(InF) ≠ '\n') {
      *InEnd↑ = ByteOf[NextCh(InF)], GetCh(InF);
      if (InEnd[-1] ≠ ' ') InLast = InEnd;
      if (InEnd ≡ InBuf + InBufN) {
         while (NextCh(InF) ≠ '\n') GetCh(InF);
      // Keep InBuf[InBufN] empty
         if (InLast > ↓InEnd) InLast = InEnd;
         InBeg = InBuf, Error(Failed, "Input line too long");
      }
   }
   GetCh(InF), InEnd = InLast;
   return true;
}

// §4. Reporting Errors to the User.
// ‹TANGLE› does the following:
// ∙	Phase I:	Scanning ≡ «·true·»: read and compress the program from WebF.
// ∙	Phase II:	Scanning ≡ «·false·»: decompress and write the program to PasF.
bool Scanning;

// Syntax errors, and their location in the input, are reported with ‛Error("Error message")’, or with ‛Fatal()’, if fatal.
// In Phase II, the location indicates refers instead to the output file.
void Error(ErrLevel Level, char *Format, ...) {
   if (Status < Level) Status = Level;
   printf("\n! ");
   va_list AP; va_start(AP, Format);
   for (char *S = Format; *S ≠ '\0'; S↑)
      if (*S ≠ '%') putchar(Ch);
      else switch (*↑S) {
         case 'S': {
            for (String S = va_arg(AP, String), EndS = S + 25; S ≤ EndS; S↑) putchar(CharOf[*S]);
         }
         break;
         case 's': { // Print an identifier or module name.
            StringP IdP = va_arg(AP, StringP);
            if (IdP ≥ StrAt) PutS("IMPOSSIBLE");
            else for (String S = *IdP; S < IdP[1]; S↑) putchar(CharOf[*S]);
         }
         break;
         case 'x': printf("%1x", (unsigned)va_arg(AP, Byte1)); break;
         case 'u': printf("%1u", (unsigned)va_arg(AP, Byte1)); break;
         case 'd': printf("%1d", va_arg(AP, int)); break;
         case 'c': putchar(CharOf[va_arg(AP, InChar)]); break;
      }
   va_end(AP);
   if (Status < Failed) return;
// Print '‹.›' and location of error message
   if (Scanning) {
   // The location is based on the input buffer.
      printf(". (%sl.%1d)\n", InDel? "change file ": "", CurY);
   // Skip down a line at the cited location and print the rest of the line directly below on a new line.
      String InS = InBeg ≥ InEnd? InEnd: InBeg;
      for (String InK = InBuf; InK < InS; InK↑) putchar(*InK ≡ TabL? " ": CharOf[*InK]);
      putchar('\n');
      for (String InK = InBuf; InK < InS; InK↑↑) putchar(' ');
      for (String InK = InS; InK < InEnd; InK↑) putchar(CharOf[*InK]);
   // Make room for subsequent messages.
      putchar(' ');
   } else {
   // The location is based on output buffer.
   // Print the partially-filled output buffer followed by "...".
      printf(". (l.%1d)\n", CurY);
      for (String ExS = ExBuf; ExS < ExEnd; ExS↑) putchar(CharOf[*ExS]);
      PutS("... ");
   }
   FlushEx();
   if (Status ≥ Killed) longjmp(ExitLab, 1);
}

// Fatal() just cuts across all active procedure levels and jumps out of the program.
// This is the only non-local goto statement in ‹TANGLE›.
// It is used when no recovery from a particular error has been provided.
#define Fatal(Msg) (Error(Killed, Msg))
// Panic mode for when ‹TANGLE› becomes completely derailed: Confusion("indication of where we are").
// This error message is meant for the ‹TANGLE› maintainer rather than the user.
#define Confusion(At) Fatal("This can't happen (" At ")")
// An overflow stop occurs if ‹TANGLE›'s tables aren't large enough.
#define OutOfMemory(Mem) Fatal("Sorry, " Mem " capacity exceeded")

// §5. Data Structures.
// Program text is pooled into the 8-bit arrays, pointed into by rasters of 16-bit pointers:
// ∙	StrPool[]: StrP[] for identifiers, strings and modules;
// ∙	TokPool[]: TokP[] for macros and module aliases;
// ∙	NextH(), TypeH(), Alias(), and MoreP() give further information about names.
// Allocation is sequential, deletions are only in Phase II and are all last-in-first-out.
typedef unsigned char Byte1;	// Unsigned one-byte quantities.
typedef unsigned int Byte2;	// Unsigned two-byte quantities.

typedef InChar *String;
InChar StrPool[0..StrMax];	// characters of names
const String StrMaxP = StrPool + StrMax;

typedef Byte1 *Token;
Byte1 TokPool[0..TokMax];	// tokens
const Token TokMaxP = TokPool + TokMax;

// Identifiers are hashed by a hash address H into hash chain FullId[H] → NextH(FullId[H]) → NextH(NextH(FullId[H])) → ⋯ → Str0.
// A StringP variable IdP points into StrP[] and is pooled in StrPool[] over the range IdP[0] to IdP[1] - 1.
// Str0 is treated as the NULL pointer and is used for undefined module names, but not for identifiers.
// StrHi is the high-water mark for StrPool[], StrAt for StrP[] and StrPEnd for strings in StrP[]; thus *StrAt ≡ StrHi is usually the case.
//
// Strings are pooled with identifiers; distinguished from identifiers by the double-quote as the first character.
#define StrLen(IdP) (IdP[1] - IdP[0])	// the length of the name *IdP.

typedef enum {0..NameN} StrIx;	// Identifies a name.

String StrHi = StrPool;			// The StrPool[] high-water mark.
String StrP[StrIx] = {StrPool,StrPool};	// StrPool[] raster; name 0 is made to be of length 0.
StringP StrAt = StrP + 1;		// The StrP[] high-water mark.
const StringP Str0 = StrP;		// The StringP NULL pointer.
const StringP StrPMax = StrP + NameN;	// The boundary of StrP[].
const StringP StrP2 = StrP + 0x100;	// The low-water mark for strings of length ≠ 1.
StringP StrPEnd = StrP2;		// The high-water mark for strings of length ≠ 1.
int StrPoolX = 271828;			// The sort of a hash for the whole string pool.

// Alias texts are pooled into TokPool[], as strings and names are in StrPool[], the corresponding type being TokenP.
// The TokenP variable TkP points into TokP and is pooled in TokPool[] over the range TkP[0] to TkP[1] - 1.
// MoreP(TkP) is used to connect text for macros that span 2 or more sections.
// Tok0 is used for undefined replacement texts.
// TokHi is the high-water mark for TokPool[], and TokAt for TokP[]; thus *TokAt ≡ TokHi is usually the case.
typedef enum {0..TextN} TokIx;	// Identifies a replacement text.
typedef Token *TokenP;

Token TokHi = TokPool;			// The TokPool[] high-water mark.
Token TokP[TokIx] = {TokPool,TokPool};	// TokPool[] raster; text 0 is made to be of length 0.
TokenP TokAt = TokP + 1;		// The TokP[] high-water mark.
const TokenP Tok0 = TokP;		// The TokenP NULL pointer.
const TokenP TokPMax = TokP + TextN;	// The boundary of TokP[].

// The identifiers types distinguished by TypeH:
// ∙ VarTK	Ordinary identifiers: capitalized with '_''s removed;
// 		Alias() links to a secondary hash table used to determine whether its first ChopN characters name a macro.
// ∙ NumTK	Numeric macros (including strings); Alias() ≡ 0x8000 + its corresponding numeric value.
// ∙ MacTK	Simple macros; Alias() ≡ its alias text; or Str0 if not yet defined.
// ∙ ParTK	Parametric macros; Alias() ≡ its alias text; or Str0 if not yet defined.
typedef enum {
   VarTK = 0,	// Ordinary identifiers.
   NumTK = 1,	// Numeric macros and strings.
   MacTK = 2,	// Simple macros.
   ParTK = 3	// Parametric macros.
} NameSpace;

// Module names and identifiers are pooled together in StrPool[], but module names are not hashed because ‹TANGLE› matches module names by their prefix.
// Instead, they put in the binary search tree with Root ≡ Sub1(Str0) and branch fields Sub0() and Sub1() that respectively overlay NextH() and TypeH().
#define Sub0(IdP)	(StrP + Link0[IdP - StrP])	// The first link in binary search tree for module names
#define Sub1(IdP)	(StrP + Link1[IdP - StrP])	// The second link in binary search tree for module names.
#define Root		(StrP + Link1[0])		// The module name search tree.

#define NextH(IdP)	(StrP + Link0[IdP - StrP])	// Hash link.
#define TypeH(IdP)	(NameSpace)(Link1[IdP - StrP])	// Type code.

Byte2 Link0[StrIx];			// NextH()/Sub0() links.
Byte2 Link1[StrIx] = {Str0 - StrP};	// TypeH()/Sub1() links: Root = Str0;	//  The binary search tree is initially emptied.
StringP Equiv[StrIx] = {Str0};		// Info corresponding to names:	Alias(Str0) = Str0;	// The undefined module has no alias.
#define Alias(IdP) (Equiv[IdP - StrP])

TokenP LinkX[TokIx] = {Tok0};		// Relates the alias texts.
#define MoreP(TkP) (LinkX[TkP - TokP])

// §6. Searching for Identifiers.
// The hash table described above is updated by IdLookUp(), which finds a given identifier and returns a pointer to its index in StrP[].
// If the identifier was not already present, it is inserted with a given TypeH() code;
// and an error message is printed if the identifier is being doubly defined.

// Because of the way ‹TANGLE›'s scanning mechanism works, it is most convenient to let IdLookUp() search for an identifier that is present in InBuf[].
// Two other global variables specify its position in the buffer: the first character is at IdBeg, and the last is at IdAt[-1].
// Furthermore, if the identifier is really a string,
// the global variable Char2s tells how many of the characters in the buffer appear twice (namely ‹@@› and ‹""›),
// since this additional information makes it easy to calculate the true length of the string.
// The final double-quote of the string is not included in its ‟identifier”, but the first one is,
// so the string length is IdAt - IdBeg - Char2s - 1.

// We have mentioned that VarTK identifiers belong to two hash tables,
// one for their true names as they appear in the ‹WEB› file and the other when they have been reduced to their first ChopN characters.
// The hash tables are kept by the method of simple chaining, where the heads of the individual lists appear in FullId[] and ChopId[].
// If H is a hash code, the primary hash table list starts at FullId[H] and proceeds through NextH() pointers;
// the secondary hash table list starts at ChopId[H] and proceeds through Alias() pointers.
// Of course, the same identifier will probably have two different values of H.

// IdLookUp() uses an auxiliary array called ChopPool[] to contain up to ChopN characters of the current identifier,
// if it is necessary to compute the secondary hash code.
// (This array could be declared local to IdLookUp(), but in general we are making all array declarations global in this program,
// because some compilers and some machine architectures make dynamic array allocation inefficient.)

String IdBeg;	// where the current identifier begins in the buffer
String IdAt;	// just after the current identifier in the buffer
InBufIx Char2s;	// correction to length in case of strings

// Initially all the hash lists are empty.
typedef enum {0..HashN} HashIx;		// for (HashIx H ∈ HashN) FullId[H] = Str0, ChopId[H] = Str0;
StringP FullId[HashIx], ChopId[HashIx];	// heads of hash lists
InChar ChopPool[0..ChopN];		// chopped identifier
const String ChopMaxP = ChopPool + ChopN;

// Here now is the main procedure for finding identifiers (and strings).
// The parameter T is set to VarTK except when the identifier is
// a macro name that is just being defined; in the latter case, T will be NumTK, MacTK, or ParTK.
StringP IdLookUp(NameSpace T) {	// finds current identifier
// Compute the length.
   InBufIx InLen = IdAt - IdBeg; // The length of the given identifier.
// Compute the hash code H.
// A simple hash code is used: If the sequence of ASCII codes is c₁ c₂ ⋯ c_m, its hash value will be (2ⁿ⁻¹ c₁ + 2ⁿ⁻² c₂ + ⋯ + c_n)%HashN.
   HashIx H = *IdBeg;	// hash code
   for (String InS = IdBeg + 1; InS < IdAt; InS↑) H = (H + H + *InS)%HashN;
// Compute the name location IdP.
// If the identifier is new, it will be placed in position IdP ≡ StrAt, otherwise IdP will point to its existing location.
   StringP IdP = FullId[H];	// where the identifier is being sought
   for (; IdP ≠ Str0; IdP = NextH(IdP)) if (StrLen(IdP) ≡ InLen) {
   // Compare name IdP with current identifier, break if equal.
      String InS = IdBeg;	// index into InBuf[]
      for (String S = *IdP; InS < IdAt ∧ *InS ≡ *S; InS↑, S↑);
      if (InS ≡ IdAt) break;	// all characters agree
   }
   if (IdP ≡ Str0) {
      IdP = StrAt;	// the current identifier is new
      NextH(IdP) = FullId[H], FullId[H] = IdP;	// Insert IdP at beginning of hash list.
   }
   if (IdP ≡ StrAt ∨ T ≠ VarTK) {
   // Update the tables and check for possible errors.
      if (IdP ≠ StrAt ∧ T ≠ VarTK ∧ TypeH(IdP) ≡ VarTK ∨ IdP ≡ StrAt ∧ T ≡ VarTK ∧ *IdBeg ≠ '"') {
      // Compute the secondary hash code H and put the first characters into the auxiliary array ChopPool[].
      // The following routine, which is called into play when it is necessary to look at the secondary hash table,
      // computes the same hash function as before (but on the chopped data),
      // and places a zero after the chopped identifier in ChopPool[] to serve as a convenient sentinel.
         String ChP = ChopPool;
         H = 0;
         for (String InS = IdBeg; InS < IdAt ∧ ChP < ChopMaxP; InS↑)
            if (*InS ≠ '_') *ChP = *InS ≥ 'a'? *InS - 'a' + 'A': *InS, H = (H + H + *ChP↑)%HashN;
         *ChP = '\0';
      }
      if (IdP ≠ StrAt) {
      // Give double-definition error, if necessary, and change IdP to type T.
      // If a nonnumeric macro has appeared before it was defined, ‹TANGLE› will still work all right;
      // after all, such behavior is typical of the replacement texts for modules, which act very much like macros.
      // However, an undefined numeric macro may not be used on the right-hand side of another numeric macro definition,
      // so ‹TANGLE› finds it simplest to make a blanket rule that numeric macros should be defined before they are used.
      // The following routine gives an error message and also fixes up any damage that may have been caused.

      // Now IdP ≠ StrAt and T ≠ VarTK.
         if (TypeH(IdP) ≡ VarTK) {
            if (T ≡ NumTK) Error(Failed, "This identifier has already appeared");
         // Remove IdP from secondary hash table.
         // When we have to remove a secondary hash entry, because a VarTK identifier is InDel to another TypeH(),
         // the hash code H and chopped identifier have already been computed.
            StringP IdQ = ChopId[H];
            if (IdQ ≡ IdP) ChopId[H] = Alias(IdP);
            else {
               for (; Alias(IdQ) ≠ IdP; IdQ = Alias(IdQ));
               Alias(IdQ) = Alias(IdP);
            }
         } else Error(Failed, "This identifier was defined before");
         TypeH(IdP) = T;
      } else {
      // Enter a new identifier into the table at position IdP.
      // The following routine could make good use of a generalized |pack| procedure
      // that puts items into just part of a packed array instead of the whole thing.
         if (T ≡ VarTK ∧ *IdBeg ≠ '"') {
         // Check for ambiguity and update secondary hash
            StringP IdQ = ChopId[H];	// where the identifier is being sought
            for (; IdQ ≠ Str0; IdQ = Alias(IdQ)) {
            // Check if IdQ conflicts with IdP.
               String S = *IdQ, ChP = ChopPool;
               for (; S < IdQ[1] ∧ ChP < ChopMaxP; S↑) {
                  Byte1 Ch = *S;	// byte being chopped
                  if (Ch ≠ '_') {
                     if (Ch ≥ 'a') Ch -= 'a' - 'A';	// Merge lowercase with uppercase.
                     if (*ChP ≠ Ch) goto Continue;
                     ChP↑;
                  }
               }
               if (S < IdQ[1] ∨ *ChP ≡ '\0')
                  Error(Failed, "Identifier conflict with %s", IdQ), IdQ = Str0;	// only one conflict will be printed, since Alias(Str0) ≡ Str0.
            Continue:
               continue;
            }
            Alias(IdP) = ChopId[H], ChopId[H] = IdP;	// put IdP at front of secondary list
         }
         String S = StrHi;	// index into StrPool[]
         if (S + InLen > StrMaxP) OutOfMemory("byte memory");
         if (StrAt ≥ StrPMax) OutOfMemory("name");
      // Get ready to move the identifier into StrPool[].
         for (String InS = IdBeg; InS < IdAt; S↑, InS↑) *S = *InS;
         *↑StrAt = StrHi = S;
         if (*IdBeg ≠ '"') TypeH(IdP) = T;
         else {
         // Define and output a new string of the pool.
         // We compute the string pool check sum by working modulo a prime number that is large but not so large that overflow might occur.
            const unsigned CheckSumPrime = 0x1fffffb7;	// 2²⁹ - 73
            TypeH(IdP) = NumTK;	// strings are like numeric macros
            if (InLen - Char2s ≡ 2)	// this string is for a single character
               Alias(IdP) = StrP + 0x8000 + IdBeg[1];
            else {
               Alias(IdP) = StrPEnd + 0x8000;
               InLen -= Char2s + 1; if (InLen ≥ 100) Error(Failed, "Preprocessed string is too long");
               StrPEnd↑, fprintf(StrF, "%c%c", CharOf['0' + InLen/10], CharOf['0' + InLen%10]);	// output the length
               for (StrPoolX += StrPoolX + InLen; StrPoolX > CheckSumPrime; StrPoolX -= CheckSumPrime);
               for (String InS = IdBeg + 1; InS < IdAt; InS↑) {
                  fputc(CharOf[*InS], StrF);	// output characters of string
                  for (StrPoolX += StrPoolX + *InS; StrPoolX > CheckSumPrime; StrPoolX -= CheckSumPrime);
                  if (*InS ≡ '"' ∨ *InS ≡ '@') InS↑; // Omit doubled '""' and '@@'.
               }
               fputc('\n', StrF);
            }
         }
      }
   }
   return IdP;
}

// §7. Searching for Module Names.
// ModLookUp() finds the module name ModPool[1..l] in the search tree, after inserting it if necessary, and returns a pointer to where it was found.

// Module names are placed into ModPool[] with consecutive spaces, tabs, and carriage-returns replaced by single spaces.
// There will be no spaces at the beginning or the end.
// (We set ModPool[0] = ' ' to facilitate this, since ModLookUp() uses ModPool[1] as the first character of the name.)
InChar ModPool[0..NameMax] = " ";	// name being sought for
const String ModEndP = ModPool + NameMax;

typedef enum {
   LtMT = 0,	// the first name is lexicographically less than the second
   EqMT = 1,	// the first name is equal to the second
   GtMT = 2,	// the first name is lexicographically greater than the second
   SubMT = 3,	// the first name is a proper prefix of the second
   SupMT = 4	// the first name is a proper extension of the second
} ModDiffT;

// The result of comparing the given name to name P.
ModDiffT MatchNames(StringP IdP, String ModEnd) {
   String S = *IdP;	// index into StrPool[]
   String ModS = ModPool + 1;	// index into ModPool[]
   for (; S < IdP[1] ∧ ModS ≤ ModEnd ∧ *ModS ≡ *S; S↑, ModS↑);
   return S ≡ IdP[1]? (ModS > ModEnd? EqMT: SupMT): ModS > ModEnd? SubMT: *ModS < *S? LtMT: GtMT;
}

// According to the rules of ‹WEB›, no module name should be a proper prefix of another, so a ‟clean” comparison should occur between any two names.
// The result of ModLookUp() is 0 if this prefix condition is violated.
// An error message is printed when such violations are detected during phase two of ‹WEAVE›.
StringP ModLookUp(String ModEnd) {	// finds module name
   ModDiffT Mt = GtMT;	// comparison between two names.
   StringP IdQ = Str0;	// father of node IdP.
   StringP IdP = Root;	// current node of the search tree: Root is the root of the tree.
   while (IdP ≠ Str0) {
      Mt = MatchNames(IdP - StrP, ModEnd), IdQ = IdP;
      if (Mt ≡ LtMT) IdP = Sub0(IdQ);
      else if (Mt ≡ GtMT) IdP = Sub1(IdQ);
      else if (Mt ≡ EqMT) return IdP;
      else { Error(Failed, "Incompatible section names"); return Str0; }
   }
// Enter a new module name into the tree.
   String SK = StrHi + (ModEnd - ModPool);		// index into StrPool[]
   if (SK > StrMaxP) OutOfMemory("byte memory");
   if (StrAt ≥ StrPMax) OutOfMemory("name");
   StringP IdP = StrAt;
   if (Mt ≡ LtMT) Sub0(IdQ) = IdP; else Sub1(IdQ) = IdP;
   Sub1(IdP) = Sub0(IdP) = Str0, Mt = EqMT, Alias(IdP) = Str0;
   for (String IdS = StrHi, ModS = ModPool + 1; ModS ≤ ModEnd; IdS↑, ModS↑) *IdS = *ModS;
   *↑StrAt = StrHi = SK;
   return IdP;
}

// PrefixLookUp() is supposed to find exactly one module name that has ModPool+1..ModEnd as a prefix.
// Actually the algorithm silently accepts also the situation that some module name is a prefix of ModPool+1..ModEnd,
// because the user who painstakingly typed in more than necessary probably doesn't want to be told about the wasted effort.
StringP PrefixLookUp(String ModEnd) {	// finds name extension
// Begin the search at the root of the tree.
   StrIx Hits = 0;	// the number of hits
   StringP IdR = Str0;	// extension found
   for (StringP IdQ = Str0, IdP = Root; IdP ≠ Str0; ) {
   // IdP: Current node of the search tree, IdQ; another place to resume the search after one branch is done.
      ModDiffT Mt = MatchNames(IdP - StrP, ModEnd);	// comparison between two names
      if (Mt ≡ LtMT) IdP = Sub0(IdP);
      else if (Mt ≡ GtMT) IdP = Sub1(IdP);
      else IdR = IdP, Hits↑, IdQ = Sub1(IdP), IdP = Sub0(IdP);
      if (IdP ≡ Str0) IdP = IdQ, IdQ = Str0;
   }
   if (Hits ≡ 0) Error(Failed, "Name does not match");
   else if (Hits > 1) Error(Failed, "Ambiguous prefix");
   return IdR;	// the result will be 0 if there was no match
}

// §8. Tokens.
// Replacement texts, which represent «Pas» code in a compressed format, appear in TokPool[] as mentioned above.
// The codes in these texts are called ‛tokens’; some tokens occupy two consecutive eight-bit byte positions, and the others take just one byte.

// If TkP ≠ Tok0 points to a replacement text, *TkP is the TokPool[] position of the first eight-bit code of that text.
// The following assumptions are made:
// ∙	MoreP(TkP) ≡ Tok0:		*TkP ≡ the replacement text for a macro.
// ∙	MoreP(TkP) ≠ Tok0:		*TkP ≡ the replacement text for a module.
//	―	MoreP(TkP) ≡ LastMod:	there is no further text for this module.
//	―	MoreP(TkP) ≠ LastMod:	the continuation of this replacement text; used for chaining the «Pas» texts of modules that span multiple sections.
// ∙	MoreP(Tok0):			the first unnamed module; chained together with the «Pas» texts of all the unnamed modules.
//	―	LastUnMod:		the most recent such pointer.
#define LastMod TokPMax	// The final MoreP() in module replacement texts.

TokenP LastUnMod = Tok0;	// The most recent replacement text of unnamed module.

// If the first byte of a token is less than 0x80, the token occupies a single byte.
// Otherwise we make a sixteen-bit token by combining two consecutive bytes A and B.
// If 0x80 ≤ A < 0xa8, then (A - 0x80)×2⁸ + B points to an identifier; if (0xa8 ≤ A < 0xd0), (A - 0xa8)×2⁸ + B points to a module name;
// otherwise, i.e., if 0xd0 ≤ A < 0x100, then (A - 0xd0)×2⁸ + B is the number of the module in which the current replacement text appears.

// Codes less than 0x80 are 7-bit ASCII codes that represent themselves.
// In particular, a single-character identifier like ‛x’ will be a one-byte token, while all longer identifiers will occupy two bytes.

// Some of the 7-bit ASCII codes will not be present in this context, however, so we can use them for special purposes.
// The following symbolic names are used:
// They take the place of NUL, ^B, ^C, '\t', '\n', '\f', '\r', ' ', '}' and DEL respectively.
#define ParL 0x00	// The insertion of a parameter.
			// Only in the replacement texts of ParTK macros, outside of single-quoted strings in those texts.
#define SetL 0x02	// The ‹@=› that begins a verbatim «Pas» string.
			// It is also used for the end of the string.
#define EolL 0x03	// ‹@\›, forces a line break in the «Pas» output.
#define EnComL 0x09	// ‹@{›, which will become either ‹{› or ‹[›.
#define DeComL 0x0a	// ‹@}›, which will become either ‹}› or ‹]›.
#define OctL 0x0c	// ‹@'›, the octal constant prefix.
#define HexL 0x0d	// ‹@"›, the hexadecimal constant prefix.
#define Dot2L 0x20	// The ‛‹..›’ in «Pas».
#define CheckSumL 0x7d	// ‹@$›, the string pool check sum.
#define JoinL 0x7f	// ‹@&›, the ‹WEB› operatio of token pasting across spaces and line breaks.

// The following procedure is used to enter a two-byte value into TokPool[] when a replacement text is being generated.
void ScanByte2(Byte2 B2) {	// stores high byte, then low byte
   if (TokHi + 2 > TokMaxP) OutOfMemory("token");
   *TokHi↑ = B2/0x100;	// this could be done by a shift command
   *TokHi↑ = B2%0x100;	// this could be done by a logical and
}

// §9. Stacks for Output.
// Let's make sure that our data structures contain enough information to produce the entire «Pas» program as desired,
// by working next on the algorithms that actually do produce that program.

// The output process uses a stack to keep track of what is going on at different ‟levels” as the macros are being expanded.
// Entries on this stack have five parts:
// ∙	End	is the TokPool[] location where the replacement text of a particular level will end;
// ∙	At	is the TokPool[] location from which the next token on a particular level will be read;
// ∙	Str	points to the name corresponding to a particular level;
// ∙	Tok	points to the replacement text currently being read at a particular level;
// ∙	Mod	is the module number, or zero if this is a macro.
// The current values of these five quantities are referred to quite frequently,
// so they are stored in a separate place instead of in QStack[].
// We call the current values CurEnd, CurAt, CurId, CurAs, and CurMod.
//
// The global variable QSP tells how many levels of output are currently in progress.
// The end of all output occurs when the QStack[] is empty, i.e., when QSP ≡ QStack.
typedef enum {0x3000} ModNumT;
typedef struct ExState {
// Cached copies of CurEnd, CurAt, CurId, CurAs and CurMod.
   Token End, At; StringP Id; TokenP As; ModNumT Mod;
} ExState;

Token CurEnd;	// The current ending location in TokPool[] of the replacement text.
Token CurAt;	// The location of next output byte within the replacement text.
StringP CurId;	// The StrP[] pointer to the current name being expanded.
TokenP CurAs;	// The TokP[] pointer to the current replacement text.
ModNumT CurMod;	// The current number of the module being expanded, or 0 if not a module.

ExState QStack[1..StackN];	// info for non-current levels
const ExState *QEndP = QStack + StackN;
ExState *QSP;		// first unused location in the output state stack

// Parameters must also be stacked.
// They are placed in TokPool[] just above the other replacement texts, and dummy parameter ‛names’ are placed in StrP[] just after the other names.
// The variables TokAt and TokHi essentially serve as parameter stack pointers during the output phase,
// so there is no need for a separate data structure to handle this problem.

// There is an implicit stack corresponding to meta-comments that are output via ‹@{› and ‹@}›}.
// But this stack need not be represented in detail, because we only need to know whether it is empty or not.
// A global variable ComLevel tells how many items would be on this stack if it were present.
Byte1 ComLevel;	// The current depth of ‹@{› ⋯ ‹@}› nesting.

// When the replacement text for name IdP is to be inserted into the output,
// the following subroutine is called to save the old level of output and get the new one going.
void PushLevel(StringP IdP) {	// suspends the current level
   if (QSP ≡ QEndP) OutOfMemory("stack");
   else
      *QSP↑ = (struct ExState){ .End: CurEnd, .At: CurAt, .Id: CurId, .As: CurAs, .Mod: CurMod},	// Save CurEnd, CurAt, etc.
      CurId = IdP, CurAs = TokP + (Alias(IdP) - StrP), CurAt = *CurAs, CurEnd = CurAs[1], CurMod = 0;
}

// When we come to the end of a replacement text, PopLevel() does the right thing:
// It either moves to the continuation of this replacement text or returns the state to the most recently stacked level.
// Part of this subroutine, which updates the parameter stack, will be given later when we study the parameter stack in more detail.
void PopLevel(void) {	// do this when CurAt reaches CurEnd.
   if (MoreP(CurAs) ≡ Tok0) {	// end of macro expansion
      if (TypeH(CurId) ≡ ParTK)
      // Remove a parameter from the parameter stack.
      // PopLevel() undoes the effect of parameter-pushing when a parameter macro is finished:
      // The maximum value of TokHi occurs just before parameter popping.
         StrAt↓, TokHi = *↓TokAt;
   } else if (MoreP(CurAs) < LastMod) {	// link to a continuation
   // We will stay on the same level
      CurAs = MoreP(CurAs), CurAt = *CurAs, CurEnd = CurAs[1];
      return;
   }
// Go down to the previous level.
   if (↓QSP > QStack) CurEnd = QSP→End, CurAt = QSP→At, CurId = QSP→Id, CurAs = QSP→As, CurMod = QSP→Mod;
}

// The heart of the output procedure is GetOutput(), which produces the next token of output that is not a reference to a macro.
// This procedure handles all the stacking and unstacking that is necessary.
// It returns the value NumL if the next output has a numeric value (the value of a numeric macro or string),
// in which case CurVal has been set to the number in question.
// The procedure also returns the value ModNumL if the next output begins or ends the replacement text of some module,
// in which case CurVal is that module's number (if beginning) or the negative of that value (if ending).
// And it returns the value IdL if the next output is an identifier of length two or more, in which case CurVal points to that identifier name.

// The codes returned by GetOutput() are:
#define NumL	0x80	// Numeric output
#define ModNumL	0x81	// Module numbers
#define IdL	0x82	// Identifiers

int CurVal;	// additional information corresponding to output token

inline void ScanByte1(InChar B1) {
   if (TokHi ≡ TokMaxP) OutOfMemory("token");
   *TokHi↑ = B1;
}

// If GetOutput() finds that no more output remains, it returns the value zero.
Byte2 GetOutput(void) {	// returns next token after macro expansion
   while (QSP > QStack) {
      while (CurAt ≡ CurEnd) {
         CurVal = -CurMod, PopLevel();
         if (CurVal ≠ 0) return ModNumL;
      }
      Byte2 B2 = *CurAt↑;	// value of current byte
      if (B2 ≡ ParL)
      // Scan the module name and make CurModule point to it.
      // When a parameter occurs in a replacement text, we treat it as a simple macro in position (StrAt - StrP - 1):
         PushLevel(StrAt - 1);
      else if (B2 < 0x80) return B2; // one-byte token
      else if (B2 < 0xa8) {
         StringP MacIdP = StrP + 0x100*(B2 - 0x80) + *CurAt↑;
         switch (TypeH(MacIdP)) { // Expand macro MacIdP and return, or continue if no output found.
            case VarTK: CurVal = MacIdP - StrP; return IdL;
            case NumTK: CurVal = Alias(MacIdP) - (StrP + 0x8000); return NumL;
            case ParTK: {
            // Put a parameter on the parameter stack, or continue if error occurs.
            // We come now to the interesting part, the job of putting a parameter on the parameter stack.
            // First we pop the stack if necessary until getting to a level that hasn't ended.
            // Then the next character must be a ‛‹(*>’;
            // and since parentheses are balanced on each level, the entire parameter must be present, so we can copy it without difficulty.
               while (CurAt ≡ CurEnd ∧ QSP > QStack) PopLevel();
               if (QSP ≡ QStack ∨ *CurAt ≠ '(') { Error(Failed, "No parameter given for %s", MacIdP); break; }
            // Copy the parameter into TokPool[].
            // Similarly, a ParL token encountered as we copy a parameter is converted into a simple macro call for StrAt - StrP - 1.
            // Some care is needed to handle cases like \{macro}|(#; PutS("#)"))|; the ‹\#› token will have been changed to ParL outside of strings,
            // but we still must distinguish ‛real’ parentheses from those in strings.
               Byte2 ParLevel = 1;	// excess of ‹(› versus ‹)› while copying a parameter
               CurAt↑;	// skip the opening ‛‹(›’
               while (true) {
                  Byte1 B1 = *CurAt↑;	// byte being copied
                  if (B1 ≡ ParL) ScanByte2(StrAt - 1 - StrP + 0x8000);
                  else {
                     if (B1 ≥ 0x80) ScanByte1(B1), B1 = *CurAt↑;
                     else switch (B1) {
                        case '(': ParLevel↑; break;
                        case ')':
                           if (↓ParLevel ≡ 0) goto Break;
                        break;
                        case '\'':
                           do ScanByte1(B1), B1 = *CurAt↑; while (B1 ≠ '\'');	// Copy the string, don't change ParLevel.
                        break;
                     }
                     ScanByte1(B1);
                  }
               }
            }
            Break: {
               Alias(StrAt) = StrP + (TokAt - TokP), TypeH(StrAt) = MacTK;
               String S = StrHi;	// index into StrPool[]
            // This code has set the parameter identifier for debugging printouts.
               if (StrAt ≥ StrPMax) OutOfMemory("name");
               *↑StrAt = S;
               if (TokAt ≥ TokPMax) OutOfMemory("text");
               MoreP(TokAt) = Tok0, *↑TokAt = TokHi;
            }
            case MacTK:
               PushLevel(MacIdP);
            break;
            default: Confusion("output"); // return MacIdP;
         }
      } else if (B2 < 0xd0) {
         StringP ModIdP = StrP + 0x100*(B2 - 0xa8) + *CurAt↑;
      // Expand module ModIdP, continue.
      // The user may have forgotten to give any «Pas» text for a module name, or the «Pas» text may have been associated with a different name by mistake.
         if (Alias(ModIdP) ≠ Str0) PushLevel(ModIdP);
         else if (ModIdP ≠ Str0) Error(Failed, "Not present: <%s>", ModIdP);
      } else {
         CurMod = CurVal = 0x100*(B2 - 0xd0) + *CurAt↑;
         return ModNumL;
      }
   }
   return 0;
}

// §10. Producing the Output.
// GetOutput() above handles most of the complexity of output generation,
// but there are two further considerations that have a nontrivial effect on ‹TANGLE›'s algorithms.

// First, we want to make sure that the output is broken into lines not exceeding LineN characters per line,
// where these breaks occur at valid places (e.g., not in the middle of a string or a constant or an identifier,
// not between ‛‹<›’ and ‛‹>›’, not at a ‛‹@&›’ position where quantities are being joined together).
// Therefore we assemble the output into a buffer before deciding where the line breaks will appear.
// However, we make very little attempt to make ‟logical” line breaks that would enhance the readability of the output;
// people are supposed to read the input of ‹TANGLE› or the «TeX» ed output of ‹WEAVE›, but not the tangled-up output.
// The only concession to readability is that a break after a semicolon will be made if possible,
// since commonly used ‟pretty printing” routines give better results in such cases.

// Second, we want to decimalize non-decimal constants, and to combine int quantities that are added or subtracted,
// because «Pas» doesn't allow constant expressions in subrange types or in case labels.
// This means we want to have a procedure that treats a construction like ‹(E-15+17)› as equivalent to ‛‹(E+2)›’,
// while also leaving ‛‹(1E-15+17)›’ and ‛‹(E-15+17*y)›’ untouched.
// Consider also ‛‹-15+17.5›’ versus ‛‹-15+17..5›’.
// We shall not combine integers preceding or following ‹*›, ‹/›, ‹div›, ‹mod›, or ‹@&›.
// Note that if |y| has been defined to equal -2, we must expand ‛‹x*y›’ into ‛‹x*(-2)›’;
// but ‛‹x - y›’ can expand into ‛‹x + 2›’ and we can even change ‛‹x - y%z›’ to ‛‹x + 2%z›’ because «Pas» has a nonstandard «·mod·» operation!

// The following solution to these problems has been adopted:
// ExBuf[] contains characters that have been generated but not yet output, and there are three pointers into this array.
// ∙	One of these, ExEnd, is the number of characters currently in the buffer, and we will have ExBuf ≤ ExEnd ≤ LineMaxP most of the time.
// ∙	The second is ExAt, which is the largest value ≤ ExEnd
//	such that we are definitely entitled to end a line by outputting the characters in ExBuf + 1 .. ExAt - 1; we will always have ExAt ≤ LineMaxP.
// ∙	Finally, ExBeg is either ExBuf or the largest known value of a legal break after a semicolon or comment on the current line;
//	we will always have ExBeg ≤ ExAt.
typedef enum {0..ExBufN} ExBufIx;
const strring ExMaxP = ExBuf + ExBufN, LineMaxP = ExBuf + LineN;
InChar ExBuf[ExBufIx];	// assembled characters
String ExEnd;	// first available place in ExBuf[]
String ExAt;	// last breaking place in ExBuf[]
String ExBeg;	// last semicolon breaking place in ExBuf[]

// Besides having those three pointers, the output process is in one of several states:
// * ValQ		a number or identifier was just buffered, so blanks or line breaks must separate it from a later number or identifier.
// * JoiningQ		‹@&› occurred after the last item buffered, which inhibits spaces between it and the next item.
// * SignQ		the last item buffered must precede a sign: '+' (if ExApp > 0) or ‛-’ (if ExApp < 0).
// * SignValQ		means that the decimal equivalent of ExVal should be appended to the buffer.
//			If ExVal < 0, or if ExVal ≡ 0 and LastSign < 0, the number should be preceded by a minus sign.
//			Otherwise it should be preceded by the character ExSign unless ExSign ≡ '\0'; the ExSign variable is either '\0' or ' ' or '+'.
// * SignValSignQ	like SignValQ, but append a sign: '+' (f ExApp > 0) or '-' (if ExApp < 0).
// * SignValValQ	like SignValQ, but append the decimal equivalent of ExApp including its sign, using LastSign in case ExApp ≡ 0.
// * MiscQ		means none of the above.
// For example, the output buffer and output state run through the following sequence as we generate characters from ‛‹(x - 15 + 19 - 2)›’:
//	output	ExBuf[]	ExQ		ExSign	ExVal	ExApp	LastSign
//	(	‹(›	MiscQ
//	x	‹x›	ValQ
//	-	‹x›	SignQ				-1	-1
//	15	‹x›	SignValQ	'+'	 -15		-15
//	+	‹x›	SignValSignQ	'+'	 -15	+1	+1
//	19	‹x›	SignValValQ	'+'	 -15	+19	+1
//	-	‹x›	SignValSignQ	'+'	 +4	-1	-1
//	2	‹x›	SignValValQ	'+'	 +4	-2	-2
//	)	‹x+2›	MiscQ
// At each stage we have put as much into the buffer as possible without knowing what is coming next.
// Examples like ‛‹x - 0.1›’ indicate why LastSign is needed to associate the proper sign with an output of zero.

// In states ValQ, JoiningQ, and MiscQ the last item in the buffer lies between ExAt and ExEnd - 1, inclusive;
// in the other states we have ExAt ≡ ExEnd.

// The numeric values assigned to ValQ, etc., have been chosen to shorten some of the program logic;
// for example, the program makes use of the fact that SignQ + 2 ≡ SignValSignQ.

// The states are linked as ValQ → SignValQ → SignValValQ → JoiningQ and SignQ → SignValSignQ.
#define MiscQ 0		// Special characters.
#define ValQ 1		// Numbers and identifiers.
#define SignQ 2		// A sign: ‹+› or ‹-›.
#define SignValQ 3	// A sign and value.
#define SignValSignQ 4	// SignValQ and a pending sign.
#define SignValValQ 5	// SignValQ and a pending value.
#define JoiningQ 6	// In concatenation: the state associated with ‹@&›.

Byte1 ExQ;		// current status of partial output
int ExVal, ExApp;	// pending values
InChar ExSign;		// sign to use if appending ExVal ≥ 0.
enum {-1,0,+1} LastSign;	// sign to use if appending a zero

// Here is a routine that is invoked when ExEnd > LineMaxP or when it is time to flush out the final line.
// FlushBuffer() often writes out the line up to the current ExAt position, then moves the remaining information to the front of ExBuf[].
// However, it prefers to write only up to ExBeg, if the residual line won't be too long.
inline void CheckBreak(void) { if (ExEnd > LineMaxP) FlushBuffer(); }

void FlushBuffer(void) {	// writes one line to output file
   String ExExAt = ExAt;	// value of ExAt upon entry
   if (ExBeg ≠ ExBuf ∧ ExEnd - ExBeg ≤ LineN) ExAt = ExBeg;
   for (String ExS = 0; ExS < ExAt; ExS↑) fputc(CharOf[*ExS], PasF);
   fputc('\n', PasF), CurY↑;
   if (CurY%100 ≡ 0) {
      putchar('.');
      if (CurY%500 ≡ 0) printf("%1d", CurY);
      FlushEx();	// progress report
   }
   if (ExAt < ExEnd) {
      if (*ExAt ≡ ' ' ∧ ↑ExAt > ExExAt) ExExAt = ExAt;	// Drop space at break
      for (String Ex0 = ExBuf, Ex1 = ExAt; Ex1 < ExEnd; Ex0↑, Ex1↑) *Ex0 = *Ex0;
   }
   ExBufIx ExLen = ExAt - ExBuf;
   ExEnd -= ExLen, ExAt = ExExAt - ExLen, ExBeg = ExBuf;
   if (ExEnd > LineMaxP) Error(Failed, "Long line must be truncated"), ExEnd = LineMaxP;
}

// Another simple and useful routine appends the decimal equivalent of a nonnegative int to the output buffer.
inline void AppCh(InChar Ch) { *ExEnd↑ = Ch; } // append a single character

void AppVal(int V) {	// Buffer V, assumes V ≥ 0.
   String ExS = ExMaxP // First we put the digits at the very end of ExBuf[].
   do *ExS↓ = V%10, V /= 10; while (V ≠ 0);
   do AppCh(*↑ExS + '0'); while (ExS ≠ ExMaxP);	// then we append them, most significant first
}

// The output states are kept up to date by SendOut(), SendVal(), and SendSign().
// SendOut() has two parameters: T tells the type of information being sent and V contains the information proper.
// Some information may also be passed in ExtraBuf[].
// Editor's Note:
// ∙	The following, not present in the original but implied by it, has been added.
typedef enum { // SendOut() codes.
   EtcQ = 0,	// The character V.
   StrQ = 1,	// String: V is the length of a string or something like ‛‹≠›’ in ExtraBuf[].
   VarQ = 2,	// Identifier: V is the length of an identifier in ExtraBuf[].
   RatQ = 3	// Fraction: V is the length of a fraction and/or exponent in ExtraBuf[].
} SendCode;

InChar ExtraBuf[1..LineN];	// a contribution to ExBuf[].
String ExtraMaxP = ExtraBuf + LineN;

// A slightly subtle point in the following code is that the user may ask for a JoinL operation (i.e., ‹@&›) following whatever is being sent out.
// We will see later that JoinL is implemented in part by calling SendOut(RatQ, 0).

// Append ExVal to buffer.
inline void BufferExVal(void) {
   if (ExVal < 0 ∨ ExVal ≡ 0 ∧ LastSign < 0) AppCh('-');
   else if (ExSign > 0) AppCh(ExSign);
   AppVal(abs(ExVal)), CheckBreak();
}

void SendOut(Byte1 T, String ExV) {	// Output string ExtraBuf+1..ExV of type T.
// Get the buffer ready for appending the new information.
// Here is where the buffer states for signs and values collapse into simpler states,
// because we are about to append something that doesn'T combine with the previous int constants.
//
// This code uses ASCII-dependencies: Since ',' - 1 ≡ '+' and ',' + 1 ≡ '-', we have ',' - c ≡ sign of c, when c ≡ ±1.
   switch (ExQ) {
      case SignValValQ:
      // Reduce SignValVal to SignVal and fall through.
         if (T ≡ RatQ ||
         // Contribution is ‹*› or ‹/› or ‹DIV› or ‹MOD›.
            T ≡ VarQ ∧ ExV ≡ ExtraBuf + 3 ∧ (
               ExV[-2] ≡ 'D' ∧ ExV[-1] ≡ 'I' ∧ *ExV ≡ 'V' ||
               ExV[-2] ≡ 'M' ∧ ExV[-1] ≡ 'O' ∧ *ExV ≡ 'D'
            ) ||
            T ≡ EtcQ ∧ (*ExV ≡ '*' ∨ *ExV ≡ '/')
         ) BufferExVal(), ExSign = '+', ExVal = ExApp;
         else ExVal += ExApp;
      case SignValQ:
         BufferExVal();
      case ValQ:
         if (T ≠ RatQ) {
            ExAt = ExEnd;
            if (T ≡ VarQ) AppCh(' ');
         }
      break;
      case SignValSignQ:
         BufferExVal();
      case SignQ:
         AppCh(',' - ExApp), CheckBreak(), ExAt = ExEnd;
      break;
      case MiscQ:
         if (T ≠ RatQ) ExAt = ExEnd;
      break;
      default:
      case JoiningQ: break;
   }
   for (String ExS = ExtraBuf + 1; ExS ≤ ExV; ExS↑) AppCh(*ExS);
   CheckBreak();
   if (T ≡ EtcQ ∧ (*ExV ≡ ';' ∨ *ExV ≡ '}')) ExAt = ExBeg = ExEnd;
   ExQ = T ≥ VarQ? ValQ: MiscQ;	// VarQ,RatQ → ValQ ∧ StrQ,EtcQ → MiscQ.
}

// The following routine is called with V ≡ ±1 when a plus or minus sign is appended to the output.
// It extends «Pas» to allow repeated signs (e.g., ‛‹↓›’ is equivalent to ‹+›), rather than to give an error message.
// The signs following ‹E› in real constants are treated as part of a fraction, so they are not seen by this routine.
void SendSign(int V) {
   switch (ExQ) {
      case SignQ: case SignValSignQ: ExApp *= V; break;
      case SignValQ: ExApp = V, ExQ = SignValSignQ; break;
      case SignValValQ: ExVal += ExApp, ExApp = V, ExQ = SignValSignQ; break;
      default: ExAt = ExEnd, ExApp = V, ExQ = SignQ; break;
   }
   LastSign = ExApp;
}

// When a (signed) int value is to be output, we call SendVal().
void SendVal(int V) {	// output the (signed) value V.
   switch (ExQ) {
      case ValQ:
      // If previous output was ‹DIV› or ‹MOD›, BadCase:.
         if (ExEnd ≡ ExAt + 3 ∨ ExEnd ≡ ExAt + 4 ∧ *ExAt ≡ ' ')
            if (
               ExEnd[-3] ≡ 'D' ∧ ExEnd[-2] ≡ 'I' ∧ ExEnd[-1] ≡ 'V' ||
               ExEnd[-3] ≡ 'M' ∧ ExEnd[-2] ≡ 'O' ∧ ExEnd[-1] ≡ 'D'
            ) goto BadCase;
         ExSign = ' ', ExQ = SignValQ, ExVal = V, ExAt = ExEnd, LastSign = +1;
      break;
      case MiscQ:
      // If previous output was ‹*› or ‹/›, BadCase:.
         if (ExEnd ≡ ExAt + 1 ∧ (*ExAt ≡ '*' ∨ *ExAt ≡ '/')) goto BadCase;
         ExSign = 0, ExQ = SignValQ, ExVal = V, ExAt = ExEnd, LastSign = +1;
      break;
   // Handle cases of SendVal() when ExQ contains a sign.
      case SignQ: ExSign = '+', ExQ = SignValQ, ExVal = ExApp*V; break;
      case SignValQ: ExQ = SignValValQ, ExApp = V, Error(Failed, "Two numbers occurred without a sign between them"); break;
      case SignValSignQ: ExQ = SignValValQ, ExApp *= V; break;
      case SignValValQ: ExVal += ExApp, ExApp = V, Error(Failed, "Two numbers occurred without a sign between them"); break;
      default:
      BadCase:	// Go here if we can't keep V in the output state.
      // Append the decimal value of V, with parentheses if negative.
         if (V ≥ 0) {
            if (ExQ ≡ ValQ) ExAt = ExEnd, AppCh(' ');
            AppVal(V), CheckBreak(), ExQ = ValQ;
         } else AppCh('('), AppCh('-'), AppVal(-V), AppCh(')'), CheckBreak(), ExQ = MiscQ;
      break;
   }
}

// §11. The Big Output Switch.
// A many-way switch is used to send the output:
void SendOutput(void) {
   while (QSP > QStack) {
      Byte1 CurCh = GetOutput();	// The latest character received.
   ReSwitch:
      switch (CurCh) {
         case '\0': break;	// this case might arise if output ends unexpectedly
      {
         String ExS = ExtraBuf;	// index into ExtraBuf[].
      // Cases related to identifiers
      // Single-character identifiers represent themselves, while longer ones appear in StrPool[].
      // All must be converted to uppercase, with underlines removed. Extremely long identifiers must be chopped.
      //
      // (Some «Pas» compilers work with lowercase letters instead of uppercase.
      // If this module of ‹TANGLE› is changed,
      // it's also necessary to change from uppercase to lowercase in the modules that are listed in the index under ‟uppercase”.)
         case 'A': case 'B': case 'C': case 'D': case 'E': case 'F': case 'G': case 'H': case 'I': case 'J': case 'K': case 'L': case 'M':
         case 'N': case 'O': case 'P': case 'Q': case 'R': case 'S': case 'T': case 'U': case 'V': case 'W': case 'X': case 'Y': case 'Z':
            *↑ExS = CurCh, SendOut(VarQ, ExS);
         break;
         case 'a': case 'b': case 'c': case 'd': case 'e': case 'f': case 'g': case 'h': case 'i': case 'j': case 'k': case 'l': case 'm':
         case 'n': case 'o': case 'p': case 'q': case 'r': case 's': case 't': case 'u': case 'v': case 'w': case 'x': case 'y': case 'z':
            *↑ExS = CurCh - 'a' + 'A', SendOut(VarQ, ExS);
         break;
         case IdL:
            for (String S = StrP[CurVal]; ExS < ExtraBuf + IdMax ∧ S < StrP[CurVal + 1]; ) {
               *↑ExS = *S↑;
               if (*ExS ≥ 'a') *ExS -= 'a' - 'A';
               else if (*ExS ≡ '_') ExS↓;
            }
            SendOut(VarQ, ExS);
         break;
      // Cases related to constants, possibly leading to GetFraction: or ReSwitch:.
      // In order to encourage portable software,
      // ‹TANGLE› complains if the constants get dangerously close to the largest value representable on a 32-bit computer 2³¹ - 1.
         case CheckSumL: SendVal(StrPoolX); break;
         case OctL: {
            int N = 0;	// number being scanned.
            CurCh = '0';
            do {
               CurCh -= '0';
               if (N ≥ 0x10000000) Error(Failed, "Constant too big"); else N = 010*N + CurCh;
               CurCh = GetOutput();
            } while (CurCh ≤ '7' ∧ CurCh ≥ '0');
            SendVal(N);
         }
         goto ReSwitch;
         case HexL: {
            int N = 0;	// number being scanned.
            CurCh = '0';
            do {
               if (CurCh ≥ 'A') CurCh += 10 - 'A'; else CurCh -= '0';
               if (N ≥ 0x8000000) Error(Failed, "Constant too big"); else N = 0x10*N + CurCh;
               CurCh = GetOutput();
            } while (CurCh ≤ 'F' ∧ CurCh ≥ '0' ∧ (CurCh ≤ '9' ∨ CurCh ≥ 'A'));
            SendVal(N);
         }
         goto ReSwitch;
         case NumL: SendVal(CurVal); break;
         case '+': case '-': SendSign(',' - CurCh); break; // -1 for '-', +1 for '+'.
         case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9': {
            int N = 0;	// number being scanned.
            do {
               CurCh -= '0';
               if (N ≥ 0xccccccc) Error(Failed, "Constant too big"); else N = 10*N + CurCh;
               CurCh = GetOutput();
            } while (CurCh ≤ '9' ∧ CurCh ≥ '0');
            SendVal(N);
            if (CurCh ≡ 'e') CurCh = 'E';
            if (CurCh ≡ 'E') goto GetFraction;
         }
         goto ReSwitch;
         case '.':
            *↑ExS = '.', CurCh = GetOutput();
            if (CurCh ≡ '.') *↑ExS = '.', SendOut(StrQ, ExS);
            else if (CurCh ≥ '0' ∧ CurCh ≤ '9') goto GetFraction;
            else { *↑ExS = '.', SendOut(EtcQ, ExS); goto ReSwitch; }
         break;
         GetFraction:	// Go here to finish scanning a real constant.
         // Special code to finish real constants.
         // The following code appears at GetFraction:, when we want to scan to the end of a real constant.
         // The characters of a fraction have already been placed in ExtraBuf..ExS-1, and CurCh is the next character.
            do {
               if (ExS < ExtraMaxP) ExS↑;
               *ExS = CurCh, CurCh = GetOutput();
               if (*ExS ≡ 'E' ∧ (CurCh ≡ '+' ∨ CurCh ≡ '-')) {
                  if (ExS < ExtraMaxP) ExS↑;
                  *ExS = CurCh, CurCh = GetOutput();
               } else if (CurCh ≡ 'e') CurCh = 'E';
            } while (CurCh ≡ 'E' ∨ CurCh ≥ '0' ∧ CurCh ≤ '9');
            if (ExS ≡ ExtraMaxP) Error(Failed, "Fraction too long");
            SendOut(RatQ, ExS);
         goto ReSwitch;
      // Cases like ‹≠› and ‹←›
         case AndL: *↑ExS = 'A', *↑ExS = 'N', *↑ExS = 'D', SendOut(VarQ, ExS); break;
         case NotL: *↑ExS = 'N', *↑ExS = 'O', *↑ExS = 'T', SendOut(VarQ, ExS); break;
         case InL: *↑ExS = 'I', *↑ExS = 'N', SendOut(VarQ, ExS); break;
         case OrL: *↑ExS = 'O', *↑ExS = 'R', SendOut(VarQ, ExS); break;
         case AssL: *↑ExS = ':', *↑ExS = '=', SendOut(StrQ, ExS); break;
         case NeL: *↑ExS = '<', *↑ExS = '>', SendOut(StrQ, ExS); break;
         case LeL: *↑ExS = '<', *↑ExS = '=', SendOut(StrQ, ExS); break;
         case GeL: *↑ExS = '>', *↑ExS = '=', SendOut(StrQ, ExS); break;
         case DefL: *↑ExS = '=', *↑ExS = '=', SendOut(StrQ, ExS); break;
         case Dot2L: *↑ExS = '.', *↑ExS = '.', SendOut(StrQ, ExS); break;
         case '\'': {
         // Send a string, ReSwitch:.
         // After sending a string, we need to look ahead at the next character, in order to see if there were two consecutive single-quote marks.
         // Afterwards we go to ReSwitch to process the next character.
            *↑ExS = '\'';
            do {
               if (ExS < ExtraMaxP) ExS↑;
               *ExS = GetOutput();
            } while (*ExS ≠ '\'' ∧ QSP > QStack);
            if (ExS ≡ ExtraMaxP) Error(Failed, "String too long");
            SendOut(StrQ, ExS), CurCh = GetOutput();
            if (CurCh ≡ '\'') ExQ = JoiningQ;
         }
         goto ReSwitch;
      // Other printable characters.
      // Please don't ask how all of the following characters can actually get through ‹TANGLE› outside of strings.
      // It seems that ‹'"'› and ‹'{'› cannot actually occur at this point of the program, but they have been included just in case ‹TANGLE› changes.
      //
      // If ‹TANGLE› is producing code for a «Pas» compiler that uses ‛‹(.›’ and ‛‹.)›’ instead of square brackets (e.g., on machines with ≪_EBCDIC_≫ code),
      // one should remove '[' and ']' from this list and put them into the preceding module in the appropriate way.
      // Similarly, some compilers want ‛‹^›’ to be converted to ‛‹@›’.
         case '!': case '"': case '#': case '$': case '%': case '&': case '(': case ')': case '*': case ',': case '/': case ':': case ';':
         case '<': case '=': case '>': case '?': case '@': case '[': case '\\': case ']': case '^': case '_': case '`': case '{': case '|'
            *↑ExS = CurCh, SendOut(EtcQ, ExS);
         break;
      // Cases involving ‹@{› and ‹@}›
      // Some «Pas» compilers do not recognize comments in braces, so the comments must be delimited by ‛‹(*›’ and ‛‹*)›’.
      // In such cases the statement ‛*ExS = '{'’ that appears here should be replaced by ‛*ExS↑ = '(', *ExS = '*'’,
      // and a similar change should be made to ‛*ExS = '}'’.
         case EnComL: *↑ExS = ComLevel↑ ≡ 0? '{': '[', SendOut(EtcQ, ExS); break;
         case DeComL:
            if (ComLevel > 0) *↑ExS = ↓ComLevel ≡ 0? '}': ']', SendOut(EtcQ, ExS);
            else Error(Failed, "Extra @}");
         break;
         case ModNumL: {
            *↑ExS = ComLevel ≡ 0? '{': '[';
            bool CurNeg = CurVal < 0;
            if (CurNeg) *↑ExS = ':', CurVal = -CurVal;
            int N = 10;
            for (; CurVal ≥ N; N *= 10);
            do N /= 10, *↑ExS = '0' + CurVal/N, CurVal %= N; while (N ≠ 1);
            if (!CurNeg) *↑ExS = ':';
            *↑ExS = ComLevel ≡ 0? '}': ']', SendOut(StrQ, ExS);
         }
         break;
         case JoinL: SendOut(RatQ, ExS), ExQ = JoiningQ; break;
         case SetL: {
         // Send verbatim string.
         // Sending a verbatim string is similar, but we don't have to look ahead.
            do {
               if (ExS < ExtraMaxP) ExS↑;
               *ExS = GetOutput();
            } while (*ExS ≠ SetL ∧ QSP > QStack);
            if (ExS ≡ ExtraMaxP) Error(Failed, "Verbatim string too long");
            SendOut(StrQ, ↓ExS);
         }
         break;
      }
         case EolL:
         // Force a line break.
            SendOut(StrQ, ExS);	// Normalize the buffer.
            while (ExEnd > ExBuf) {
               if (ExEnd ≤ LineMaxP) ExAt = ExEnd;
               FlushBuffer();
            }
            ExQ = MiscQ;
         break;
         default: Error(Failed, "Can't output ASCII code %x", CurCh); break;
      }
   }
}

// §12. Introduction to the Input Phase.
// We have now seen that ‹TANGLE› will be able to output the full «Pas» program, if we can only get that program into the byte memory in the proper format.
// The input process is something like the output process in reverse, since we compress the text as we read it in and we expand it as we write it out.

// There are three main input routines.
// The most interesting is the one that gets the next token of a «Pas» text; the other two are used to scan rapidly past «TeX» text in the ‹WEB› source code.
// One of the latter routines will jump to the next token that starts with ‛‹@›’, and the other skips to the end of a «Pas» comment.

// But first we need to consider the low-level routine GetLine() that takes care of merging DelF into WebF.
// GetLine() also updates the line numbers for error messages.
int CurY;	// the number of the current line in the current file
int ExY;	// the number of the current line in the input file that is not currently being read
String InEnd;	// the last character position occupied in the buffer
String InBeg;	// the next character position to be read from the buffer
bool InEnded;	// true, if there is no more input.
bool InDel;	// true, if the current line is from DelF.

// As we toggle InDel, we must remember to swap the values of CurY and ExY so that Error() will be sure to report the correct line number.
inline void ToggleDel(void) { // CurY ↔ ExY
   InDel = !InDel;
   int TempY = ExY;	// Used when interchanging CurY with ExY.
   ExY = CurY, CurY = TempY;
}

// When !InDel, the next line of DelF is kept in DelBuf[0..(DelEnd - InBuf)], for purposes of comparison with the next line of WebF.
// After the change file has been completely input, we set DelEnd = InBuf, so that no further matches will be made.
InChar DelBuf[InBufIx];
String DelEnd;	// the last position occupied in InBuf[] before InBuf[] was swapped out to DelBuf[].

// Here's a simple function that checks if the two buffers are different.
bool LinesDontMatch(void) {
   if (DelEnd ≠ InEnd) return true;
   if (InEnd > InBuf) for (String InP = InBuf, DelP = DelBuf; InP < InEnd; InP↑, DelP↑) if (*DelP ≠ *InP) return true;
   return false;
}

// Move InBuf and InEnd to DelBuf and DelEnd.
inline void MoveBufToDel(void) {
   DelEnd = InEnd;
   if (InEnd > InBuf) for (String InP = InBuf, DelP = DelBuf; InP < InEnd; InP↑, DelP↑) *DelP = *InP;
}

// PreSetDelBuf() sets DelBuf[] in preparation for the next matching operation.
// Since blank lines in the change file are not used for matching, we have DelEnd ≡ InBuf ∧ !InDel if and only if the change file is exhausted.
// This procedure is called only when InDel; hence error messages will be reported correctly.
void PreSetDelBuf(void) {
   DelEnd = InBuf;	// this value will be used if the change file ends
// Skip over comment lines in the change file; return if end of file.
// While looking for a line that begins with ‹@x› in the change file, we allow lines that begin with ‹@›,
// as long as they don't begin with ‹@y› or ‹@z›(which would probably indicate that the change file is fouled up).
   while (true) {
      CurY↑;
      if (!ReadLine(DelF)) return;
      if (InEnd < InBuf + 2) continue;
      if (InBuf[0] ≠ '@') continue;
      if (InBuf[1] ≥ 'X' ∧ InBuf[1] ≤ 'Z') InBuf[1] += 'z' - 'Z';	// lowercasify
      if (InBuf[1] ≡ 'x') break;
      if (InBuf[1] ≡ 'y' ∨ InBuf[1] ≡ 'z') InBeg = InBuf + 2, Error(Failed, "Where is the matching @x?");
   }
// Skip to the next nonblank line; return if end of file.
// Here we are looking at lines following the ‹@x›.
   do {
      CurY↑;
      if (!ReadLine(DelF)) { Error(Failed, "Change file ended after @x"); return; }
   } while (InEnd ≡ InBuf);
   MoveBufToDel();
}

// The following procedure is used to see if the next change entry should go into effect; it is called only when !InDel.
// The idea is to test whether or not the current contents of InBuf[] matches the current contents of DelBuf[].
// If not, there's nothing more to do; but if so, a change is called for: All of the text down to the ‹@y› is supposed to match.
// An error message is issued if any discrepancy is found.
// Then the procedure prepares to read the next line from DelF.
void CheckDel(void) {	// switches to DelF if the buffers match
   if (LinesDontMatch()) return;
   int n = 0;		// the number of discrepancies found
   while (true) {
      ToggleDel();	// now it's true.
      CurY↑;
      if (!ReadLine(DelF)) {
         Error(Failed, "Change file ended before @y"), DelEnd = InBuf, ToggleDel();	// false again.
         break;
      }
   // If the current line starts with ‹@y›, report any discrepancies and return.
      if (InEnd > InBuf + 1 ∧ InBuf[0] ≡ '@') {
         if (InBuf[1] ≥ 'X' ∧ InBuf[1] ≤ 'Z') InBuf[1] += 'z' - 'Z';	// lowercasify
         if (InBuf[1] ≡ 'x' ∨ InBuf[1] ≡ 'z') InBeg = InBuf + 2, Error(Failed, "Where is the matching @y?");
         else if (InBuf[1] ≡ 'y') {
            if (n > 0) InBeg = InBuf + 2, Error(Failed, "Hmm... %d of the preceding lines failed to match", n);
            break;
         }
      }
      MoveBufToDel(), ToggleDel();	// now it's false.
      CurY↑;
      if (!ReadLine(WebF)) { Error(Failed, "WEB file ended during a change"), InEnded = true; break; }
      if (LinesDontMatch()) n↑;
   }
}

// GetLine() is called when InBeg > InEnd; it puts the next line of merged input into the buffer and updates the other variables appropriately.
// A space is placed at the right end of the line.
void GetLine(void) {	// inputs the next line
   if (InDel) {
   // Read from DelF and maybe turn off InDel.
   GetDelLine:
      CurY↑;
      if (!ReadLine(DelF)) Error(Failed, "Change file ended without @z"), InBuf[0] = '@', InBuf[1] = 'z', InEnd = InBuf + 2;
      if (InEnd > InBuf + 1 ∧ InBuf[0] ≡ '@') {	// Check if the change has ended.
         if (InBuf[1] ≥ 'X' ∧ InBuf[1] ≤ 'Z') InBuf[1] += 'z' - 'Z';	// lowercasify
         if (InBuf[1] ≡ 'x' ∨ InBuf[1] ≡ 'y') InBeg = InBuf + 2, Error(Failed, "Where is the matching @z?");
         else if (InBuf[1] ≡ 'z') PreSetDelBuf(), ToggleDel();
      }
   }
   if (!InDel) {
   // Read from WebF and maybe turn on InDel.
      CurY↑;
      if (!ReadLine(WebF)) InEnded = true;
      else if (InEnd ≡ DelEnd ∧ InBuf[0] ≡ DelBuf[0] ∧ DelEnd > InBuf) CheckDel();
      if (InDel) goto GetDelLine;
   }
   InBeg = InBuf, *InEnd = ' ';
}

// Important milestones are reached during the input phase when certain control codes are sensed.

// Control codes in ‹WEB› begin with ‛‹@›’, and the next character identifies the code.
// Some of these are of interest only to ‹WEAVE›, so ‹TANGLE› ignores them;
// the others are converted by ‹TANGLE› into internal code numbers by ControlCode() below.
// The ordering of these internal code numbers has been chosen to simplify the program logic;
// larger numbers are given to the control codes that denote more significant milestones.

#define SkipCQ 0	// Control codes of no interest to ‹TANGLE›.
#define ControlCQ 0x83	// ‛‹@t›’, ‛‹@^›’, etc.
#define FormatCQ 0x84	// ‛‹@f›’
#define DefineCQ 0x85	// ‛‹@d›’
#define ModCodeCQ 0x86	// ‛‹@p›’
#define ModNameCQ 0x87	// ‛‹@<›’
#define NewModCQ 0x88	// ‛‹@\›’ and ‛‹@*›’

Byte1 ControlCode(InChar Ch) {	// convert Ch after ‹@›
   switch (Ch) {
      case '@': return '@';				// ‹@@›: ‛@’, itself.
      case '\'': return OctL;				// ‹@'›: octal constant prefix.
      case '"': return HexL;				// ‹@"›: hexadecimal constant prefix.
      case '$': return CheckSumL;			// ‹@$›: string pool check sum prefix.
      case '*': printf("*%1d", ModNum + 1), FlushEx();	// ‹@*›: begin a new module with progress report.
      case ' ': case '\t': return NewModCQ;		// ‹@ ›: begin a new module.
      case 'D': case 'd': return DefineCQ;		// ‹@d›‹@D›: macro definition
      case 'F': case 'f': return FormatCQ;		// ‹@f›‹@F›: format definition
      case '{': return EnComL;				// ‹@{›: begin a comment
      case '}': return DeComL;				// ‹@}›: end a comment
      case 'P': case 'p': return ModCodeCQ;		// ‹@p›‹@P›: module code in an unnamed module
      case 'T': case 't':				// ‹@t›‹@T›: control text embedded in module code.
      case '^': case '.': case ':': return ControlCQ;	// ‹@^›‹@.›‹@:›: index entry: normal, typewriter, user fonts.
      case '&': return JoinL;				// ‹@&›: token paste.
      case '<': return ModNameCQ;			// ‹@<›: begin a module name.
      case '=': return SetL;				// ‹@=›: begin verbatim code.
      case '\\': return EolL;				// ‹@\›: line break in module code.
   // case '>': return SkipCQ;				// ‹@>›: end module name ― ignore.
   // case '!': case '?': return SkipCQ;		// ‹@!›‹@?›: definition flag on/off ― ignore.
   // case ',': case '/': return SkipCQ;		// ‹@,›‹@/›: thin space, line break in module code ― ignore.
   // case '|': case ';': return SkipCQ;		// ‹@|›‹@;›: math formula break, invisible semicolon ― ignore.
   // case '#': case '+': return SkipCQ;		// ‹@#›‹@+›: vertical space, line paste ― ignore.
   // case '0': case '1': case '2': return SkipCQ;	// ‹@0›‹@1›‹@2›: debug-only control codes ― ignore.
      default: return SkipCQ;				// ignore all other cases.
   }
}

// Read through the input at fairly high speed until finding the next non-ignorable control code, which it returns.
Byte1 SkipAhead(void) {	// skip to next control code
   while (true) {
      if (InBeg > InEnd) {
         GetLine();
         if (InEnded) return NewModCQ;
      }
      InEnd[1] = '@';
      for (; *InBeg ≠ '@'; InBeg↑);
      if (InBeg ≤ InEnd) {
         InBeg += 2;
         Byte1 Ch = ControlCode(InBeg[-1]);
         if (Ch ≠ SkipCQ ∨ InBeg[-1] ≡ '>') return Ch;
      }
   }
}

// SkipComment() reads through the input at somewhat high speed until finding the first unmatched right brace or until coming to the end of the file.
// It ignores characters following ‛‹\›’ characters, since all braces that aren't nested are supposed to be hidden in that way.
// For example, consider the process of skipping the first comment below,
// where the string containing the right brace has been typed as ‹‛\.\›’} in the ‹WEB› file.
void SkipComment(void) {	// Skips to next unmatched ‛\.\}’.
   Byte1 ParLevel = 0;	// excess of left braces
   while (true) {
      if (InBeg > InEnd) {
         GetLine();
         if (InEnded) { Error(Failed, "Input ended in mid-comment"); return; }
      }
      InChar Ch = *InBeg↑;	// current character
   // Do special things when Ch ≡ '@', '\', '{', '}'; return at end.
      if (Ch ≡ '@') {
         Ch = *InBeg;
         if (Ch ≠ ' ' ∧ Ch ≠ '\t' ∧ Ch ≠ '*' ∧ Ch ≠ 'z' ∧ Ch ≠ 'Z') InBeg↑;
         else { Error(Failed, "Section ended in mid-comment"), InBeg↓; return; }
      } else if (Ch ≡ '\\' ∧ *InBeg ≠ '@') InBeg↑
      else if (Ch ≡ '{') ParLevel↑
      else if (Ch ≡ '}') {
         if (ParLevel ≡ 0) return;
         ParLevel↓;
      }
   }
}

// §13. Inputting the Next Token.
// As stated above, ‹TANGLE›'s most interesting input procedure is GetTok() that inputs the next token.
// However, the procedure isn't especially difficult.

// In most cases the tokens output by GetTok() have the form used in replacement texts, except that two-byte tokens are not produced.
// An identifier that isn't one letter long is represented by the output ‛IdL’,
// and in such a case the global variables IdBeg and IdAt will have been set to the appropriate values needed by IdLookUp().
// A string that begins with a double-quote is also considered an IdL, and in such a case the global variable Char2s will also have been set appropriately.
// Control codes produce the corresponding output of ControlCode() above;
// and if that code is ModNameCQ, the value of CurModule will point to the StrP[] entry for that module name.

StringP CurModule;		// The name of module just scanned.

// Editor's Note:
// ∙	This routine, not present in the original, was added so that it could be put into the conditional of the while loop where it is being used.
bool GetNextCh(Byte1 *ChP) {
   if (InBeg > InEnd) {
      GetLine();
      if (InEnded) return false;
   }
   *ChP = *InBeg↑;
   return true;
}

// At the top level, GetTok() is a multi-way switch based on the next character in InBuf[].
// A NewModCQ code is inserted at the very end of the input file.
Byte1 GetTok(void) {	// produces the next input token
// Another global variable, InHex, is true during the time that the letters ‹A› through ‹F› should be treated as if they were digits.
   static bool InHex = false;	// True if we scanning a hexadecimal constant.
   for (Byte1 Ch; GetNextCh(&Ch); ) {
      if (InHex) {
      // Return Ch if Ch is a hexadecimal digit, otherwise set InHex = false.
         InHex = Ch ≥ '0' ∧ Ch ≤ '9' ∨ Ch ≥ 'A' ∧ Ch ≤ 'F';
         if (InHex) return Ch;
      }
      switch (Ch) {
         case 'E': case 'e':
            if (InBeg ≥ InBuf + 2 ∧ InBeg[-2] ≤ '9' ∧ InBeg[-2] ≥ '0') return 'E';	// exponent of a real constant
         case 'A': case 'B': case 'C': case 'D':/*case 'E':*/case 'F': case 'G': case 'H': case 'I': case 'J': case 'K': case 'L': case 'M':
         case 'N': case 'O': case 'P': case 'Q': case 'R': case 'S': case 'T': case 'U': case 'V': case 'W': case 'X': case 'Y': case 'Z':
         case 'a': case 'b': case 'c': case 'd':/*case 'e':*/case 'f': case 'g': case 'h': case 'i': case 'j': case 'k': case 'l': case 'm':
         case 'n': case 'o': case 'p': case 'q': case 'r': case 's': case 't': case 'u': case 'v': case 'w': case 'x': case 'y': case 'z':
         // Get an identifier.
         // We have to look at the preceding character to make sure this isn't part of a real constant,
         // before trying to find an identifier starting with ‛‹e›’ or ‛‹E›’.
            IdBeg = ↓InBeg;
            for (Byte1 Ch1; (Ch1 = *↑InBeg) ≥ '0' ∧ (Ch1 ≤ '9' ∨ Ch1 ≥ 'A') ∧ (Ch1 ≤ 'Z' ∨ Ch1 ≥ 'a') ∧ Ch1 ≤ 'z' ∨ Ch1 ≡ '_');
            if (InBeg > IdBeg + 1) { IdAt = InBeg; return IdL; }
         return Ch;
         case '"':
         // Get a preprocessed string.
         // A string that starts and ends with double-quote marks is converted into an identifier
         // that behaves like a numeric macro by means of the following piece of the program.
            Char2s = 0, IdBeg = InBeg - 1;
            do {
               Byte1 Ch1 = *InBeg↑;	// the next character
               if (Ch1 ≡ '"' ∨ Ch1 ≡ '@') {
                  if (*InBeg ≡ Ch1) InBeg↑, Ch1 = '\0', Char2s↑;
                  else if (Ch1 ≡ '@') Error(Failed, "Double @ sign missing");
               } else if (InBeg > InEnd) Error(Failed, "String constant didn't end"), Ch1 = '"';
            } while (Ch1 ≠ '"');
            IdAt = InBeg - 1;
         return IdL;
         case '@':
         // Get control code and possible module name.
         // After an ‹@› sign has been scanned, the next character tells us whether there is more work to do.
            Ch = ControlCode(*InBeg↑);
            if (Ch ≡ SkipCQ) break;
            else if (Ch ≡ HexL) { InHex = true; return Ch; }
            else if (Ch ≡ ModNameCQ) {
            // Start scanning current macro parameter, break.
            // Put module name into ModPool+1..ModK.
               String ModK = ModPool;	// indices into ModPool[]
               while (true) {
                  if (InBeg > InEnd) {
                     GetLine();
                     if (InEnded) { Error(Failed, "Input ended in section name"); break; }
                  }
                  Byte1 Ch1 = *InBeg;	// the next character
               // If end of name, break;
                  if (Ch1 ≡ '@') {
                     Ch1 = InBeg[1];
                     if (Ch1 ≡ '>') { InBeg += 2; break; }
                     else if (Ch1 ≡ ' ' ∨ Ch1 ≡ '\t' ∨ Ch1 ≡ '*') { Error(Failed, "Section name didn't end"); break; }
                     *↑ModK = '@', InBeg↑;	// Now Ch1 ≡ *InBeg again.
                  }
                  InBeg↑;
                  if (ModK < ModEndP - 1) ModK↑;
                  if (Ch1 ≡ ' ' ∨ Ch1 ≡ '\t') {
                     Ch1 = ' ';
                     if (ModK[-1] ≡ ' ') ModK↓;
                  }
                  *ModK = Ch1;
               }
            // Check for overlong name
               if (ModK ≥ ModEndP - 2) Error(Warned, "Section name too long: %S...", ModPool);
               if (*ModK ≡ ' ' ∧ ModK > ModPool) ModK↓;
               CurModule = ModK > ModPool + 3 ∧ *ModK ≡ '.' ∧ ModK[-1] ≡ '.' ∧ ModK[-2] ≡ '.'? PrefixLookUp(ModK - 3): ModLookUp(ModK);
               return Ch;
            } else if (Ch ≡ ControlCQ) {
               do Ch = SkipAhead(); while (Ch ≡ '@');
               if (InBeg[-1] ≠ '>') Error(Failed, "Improper @ within control text");
            } else return Ch;
         break;
      // Compress two-symbol combinations like ‛‹==›’.
      // Note that the following code substitutes ‹@{› and ‹@}› for the respective combinations ‛‹(*›’ and ‛‹*)›’.
      // Explicit braces should be used for «TeX» comments in «Pas» text.
         case '.': switch (*InBeg) {
            case '.': if (InBeg ≤ InEnd) { InBeg↑; return Dot2L; } else break;
            case ')': if (InBeg ≤ InEnd) { InBeg↑; return ']'; } else break;
         }
         return Ch;
         case ':': switch (*InBeg) {
            case '=': if (InBeg ≤ InEnd) { InBeg↑; return AssL; } else break;
         }
         return Ch;
         case '=': switch (*InBeg) {
            case '=': if (InBeg ≤ InEnd) { InBeg↑, return DefL; } else break;
         }
         return Ch;
         case '>': switch (*InBeg) {
            cae '=': if (InBeg ≤ InEnd) { InBeg↑; return GeL; } else break;
         }
         return Ch;
         case '<': switch (*InBeg) {
            case '=': if (InBeg ≤ InEnd) { InBeg↑; return LeL; } else break;
            case '>': if (InBeg ≤ InEnd) { InBeg↑; return NeL; } else break;
         }
         return Ch;
         case '(': switch (*InBeg) {
            case '*': if (InBeg ≤ InEnd) { InBeg↑; return EnComL; } else break;
            case '.': if (InBeg ≤ InEnd) { InBeg↑; return '['; } else break;
         }
         return Ch;
         case '*': switch (*InBeg) {
            case ')': if (InBeg ≤ InEnd) { InBeg↑; return DeComL; } else break;
         }
         return Ch;
         case ' ': case '\t': break;	// ignore spaces and tabs
         case '{': SkipComment(); break;
         case '}': Error(Failed, "Extra }"); break;
         default:
            if (Ch < 0x80) return Ch;
         break;	// ignore nonstandard characters
      }
   }
   return NewModCQ;
}

// §14. Scanning a Numeric Definition.
// When ‹TANGLE› looks at the «Pas» text following the ‛\.=’ of a numeric macro definition,
// it calls ScanNumeric(IdP), where IdP points to the name that is to be defined.
// This procedure evaluates the right-hand side,
// which must consist entirely of int constants and defined numeric macros connected with ‹+› and ‹-› signs (no parentheses).
// It also sets the global variable NextTok to the control code that terminated this definition.

// A definition ends with the control codes DefineCQ, FormatCQ, ModNameCQ, ModCodeCQ, and NewModCQ,
// all of which can be recognized by the fact that they are the largest values GetTok() can return.
#define EndOfDef(C) ((C) ≥ FormatCQ)	// is C a control code ending a definition?

Byte1 NextTok;	// control code waiting to be acted upon

// The evaluation of a numeric expression makes use of two variables called the EqVal and the NextSign.
// At the beginning, EqVal is zero and NextSign is +1.
// When a ‹+› or ‹-› is scanned, NextSign is multiplied by the value of that sign.
// When a numeric value is scanned, it is multiplied by NextSign and added to the EqVal, then NextSign is reset to $+1$.
void ScanNumeric(StringP IdP) {	// defines numeric macros
// Set EqVal to the value of the right-hand side.
   int EqVal = 0;	// accumulates sums
   enum {-1,0,+1} NextSign = +1;	// sign to attach to next value
   while (true) {
      NextTok = GetTok();
   ReSwitch:
      switch (NextTok) {
         case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9': {
         // Set Val to value of decimal constant, and set NextTok to the following token.
            int Val = 0;	// constants being evaluated
            do Val = 10*Val + NextTok - '0', NextTok = GetTok(); while (NextTok ≤ '9' ∧ NextTok ≥ '0');
            EqVal += NextSign*Val, NextSign = +1;
         }
         goto ReSwitch;
         case OctL: {
         // Set Val to value of octal constant, and set NextTok to the following token.
            int Val = 0;	// constants being evaluated
            NextTok = '0';
            do Val = 010*Val + NextTok - '0', NextTok = GetTok(); while (NextTok ≤ '7' ∧ NextTok ≥ '0');
            EqVal += NextSign*Val, NextSign = +1;
         }
         goto ReSwitch;
         case HexL: {
         // Set Val to value of hexadecimal constant, and set NextTok to the following token.
            int Val = 0;	// constants being evaluated
            NextTok = '0';
            do {
               if (NextTok ≥ 'A') NextTok += '0' + 10 - 'A';
               Val = 0x10*Val + NextTok - '0', NextTok = GetTok();
            } while (NextTok ≤ 'F' ∧ NextTok ≥ '0' ∧ (NextTok ≤ '9' ∨ NextTok ≥ 'A'));
            EqVal += NextSign*Val, NextSign = +1;
         }
         goto ReSwitch;
         case IdL: {
            StringP IdQ = IdLookUp(VarTK);	// points to identifiers being evaluated
            if (TypeH(IdQ) ≠ NumTK) {
               NextTok = '*'; goto ReSwitch;	// leads to error
            }
            EqVal += NextSign*(Alias(IdQ) - (StrP + 0x8000)), NextSign = +1;
         }
         break;
         case '+': break;
         case '-': NextSign = -NextSign; break;
         case FormatCQ: case DefineCQ: case ModCodeCQ: case ModNameCQ: case NewModCQ: goto Break;
         case ';': Error(Failed, "Omit semicolon in numeric definition"); break;
         default:
         // Signal error, flush the rest of the definition.
            Error(Failed, "Improper numeric definition will be flushed");
            do NextTok = SkipAhead(); while (!EndOfDef(NextTok));
            if (NextTok ≡ ModNameCQ) InBeg -= 2, NextTok = GetTok();	// We want to scan the module name too.
            EqVal = 0;
         goto Break;
      }
   }
Break:
   if (abs(EqVal) ≥ 0x8000) Error(Failed, "Value too big: %d", EqVal), EqVal = 0;
   Alias(IdP) = StrP + 0x8000 + EqVal;	// Name IdP now is defined to equal EqVal.
}

// §15. Scanning a Macro Definition.
// The rules for generating the replacement texts corresponding to MacTK macros, ParTK macros, and «Pas» texts of a module are almost identical,
// so a single procedure is used for all three cases.
// The differences are that
// a)	The sign # denotes a parameter only when it appears outside of strings in a ParTK macro; otherwise it stands for the ASCII character #.
//	(This is not used in standard «Pas», but some «Pas»s allow, for example, ‛‹#›’ after a certain kind of file name.)
// b)	Module names are not allowed in simple macros or ParTK macros;
//	in fact, the appearance of a module name terminates such macros and denotes the name of the current module.
// c)	The symbols ‹@d› and ‹@f› and ‹@p› are not allowed after module names, while they terminate macro definitions.

// Therefore the routine ScanAlias(), whose parameter t, specifies either MacTK or ParTK or ModNameCQ.
// Afterwards, CurAlias will point to the replacement text just generated, and NextTok will contain the control code that terminated the activity.
TokenP CurAlias;	// Replacement text formed by ScanAlias().

void ScanAlias(Byte1 t) {	// creates a replacement text
   Byte2 a;	// the current token
   Byte1 ParLevel = 0;	// left parentheses minus right parentheses
   while (true) {
      switch (a = GetTok()) {
         case '(': ParLevel↑; break;
         case ')':
            if (ParLevel ≡ 0) Error(Failed, "Extra )");
            else ParLevel↓;
         break;
         case '\'': {
         // Copy a string from the buffer to TokPool[].
            InChar b = '\'';	// a character from the buffer
            while (true) {
               ScanByte1(b);
               if (b ≡ '@')
                  if (*InBeg ≡ '@') InBeg↑;	// store only one ‹@›
                  else Error(Failed, "You should double @ signs in strings");
               if (InBeg ≡ InEnd) Error(Failed, "String didn't end"), *InBeg = '\'', InBeg[1] = '\0';
               b = *InBeg↑;
               if (b ≡ '\'')
                  if (*InBeg ≠ '\'') break;
                  else InBeg↑, ScanByte1('\'');
            }
         }
         // Now a holds the final '\'' that will be stored.
         break;
         case '#':
            if (t ≡ ParTK) a = ParL;
         break;
      // In cases that a is a non-ASCII token (IdL, ModNameCQ, etc.), either process it and change a to a byte that should be stored, or continue;
      // if a should be ignored, or break; if a signals the end of this replacement text.
         case IdL: a = IdLookUp(VarTK) - StrP, ScanByte1(a/0x100 + 0x80), a %= 0x100; break;
         case ModNameCQ:
            if (t ≠ ModNameCQ) goto Break;
            ScanByte1((CurModule - StrP)/0x100 + 0xa8), a = (CurModule - StrP)%0x100;
         break;
         case SetL:
         // Copy verbatim string from the buffer to TokPool[].
            ScanByte1(SetL), InEnd[1] = '@';
            while (true)
               if (*InBeg ≠ '@') ScanByte1(*InBeg↑);
               else if (InBeg < InEnd ∧ InBeg[1] ≡ '@') ScanByte1('@'), InBeg += 2;
               else break;
            if (InBeg ≥ InEnd) Error(Failed, "Verbatim string didn't end");
            else if (InBeg[1] ≠ '>') Error(Failed, "You should double @ signs in verbatim strings");
            InBeg += 2;
         // Another SetL byte will be stored, since a ≡ SetL.
         break;
         case FormatCQ: case DefineCQ: case ModCodeCQ:
            if (t ≠ ModNameCQ) goto Break;
            Error(Failed, "@%c is ignored in Pascal text", InBeg[-1]);
         continue;
         case NewModCQ: goto Break;
      }
      ScanByte1(a);	// Store a in TokPool[].
   }
Break:
   NextTok = a;
// Make sure the parentheses balance.
   if (ParLevel > 0) {
      if (ParLevel ≡ 1) Error(Failed, "Missing )"); else Error(Failed, "Missing %u )'s", ParLevel);
      for (; ParLevel > 0; ParLevel↓) ScanByte1(')'):
   }
   if (TokAt ≥ TokPMax) OutOfMemory("text");
   CurAlias = TokAt, *↑TokAt = TokHi;
}

// The following procedure is used to define a MacTK or ParTK macro, just after the ‛‹≡›’ of its definition has been scanned.
void DefineMacro(NameSpace T) {
   StringP IdP = IdLookUp(T);	// the identifier being defined
   ScanAlias(t), Alias(IdP) = StrP + (CurAlias - TokP), MoreP(CurAlias) = Tok0;
}

// §16. Scanning a Module.
// ScanModule() starts when ‛‹@\›’ or ‛‹@*›’ has been sensed in the input, and it proceeds until the end of that module.
// It uses ModNum to keep track of the current module number; with luck, ‹WEAVE› and ‹TANGLE› will both assign the same numbers to modules.
ModNumT ModNum;	// the current module number

// The top level of ScanModule() is trivial.
void ScanModule(void) {
   ModNum↑;
// Scan the definition part of the current module.
   NextTok = 0;
   while (true) {
      while (NextTok ≤ FormatCQ) {
         NextTok = SkipAhead();
         if (NextTok ≡ ModNameCQ)	// we want to scan the module name too
            InBeg -= 2, NextTok = GetTok();
      }
      if (NextTok ≠ DefineCQ) break;
      NextTok = GetTok();	// get identifier name
      if (NextTok ≠ IdL) { Error(Failed, "Definition flushed, must start with identifier of length > 1"); continue; }
      NextTok = GetTok();	// get token after the identifier
      if (NextTok ≡ '=') { ScanNumeric(IdLookUp(NumTK)); continue; }
      else if (NextTok ≡ DefL) { DefineMacro(MacTK); continue; }
   // If the next text is ‛(#)≡==’, call DefineMacro() and continue.
      else if (NextTok ≡ '(' ∧ (NextTok = GetTok()) ≡ '#' ∧ (NextTok = GetTok()) ≡ ')') {
         NextTok = GetTok();
         if (NextTok ≡ '=') Error(Failed, "Use ≡ for macros"), NextTok = DefL;
         if (NextTok ≡ DefL) { DefineMacro(ParTK); continue; }
      }
      Error(Failed, "Definition flushed since it starts badly");
   }
// Scan the «PASCAL»« »part of the current module.
   StringP IdP;	// module name for the current module
   switch (NextTok) {
      case ModCodeCQ: IdP = Str0; break;
      case ModNameCQ:
         IdP = CurModule;
      // Check that ‹=› or ‹≡› follows this module name, otherwise return.
         do NextTok = GetTok(); while (NextTok ≡ '+');	// allow optional ‛‹+=›’
         if (NextTok ≠ '=' ∧ NextTok ≠ DefL) {
            Error(Failed, "Pascal text flushed, ≡ sign is missing");
            do NextTok = SkipAhead(); while (NextTok ≠ NewModCQ);
            return;
         }
      break;
      default: return;
   }
// Insert the module number into TokPool[].
   ScanByte2(0xd000 + ModNum);	// 0xd000 ≡ 0xd0×0x100.
   ScanAlias(ModNameCQ);	// Now CurAlias points to the replacement text.
// Update the data structure so that the replacement text is accessible.
   if (IdP ≡ Str0) LastUnMod = MoreP(LastUnMod) = CurAlias;	// unnamed module
   else if (Alias(IdP) ≡ StrP) Alias(IdP) = StrP + (CurAlias - TokP);	// first module of this name
   else {
      IdP = Alias(IdP);
      for (; MoreP(TokP) < LastMod; IdP = StrP + (MoreP(TokP + (IdP - StrP)) - TokP));	// find end of list
      MoreP(IdP) = CurAlias;
   }
   MoreP(CurAlias) = LastMod;	// mark this replacement text as a nonmacro
}

// §17. Debugging.
// All items related to DEBUG have been removed.

// §18. The Main Program.
// We have defined plenty of procedures, and it is time to put the last pieces of the puzzle in place.
// Here is where ‹TANGLE› starts, and where it ends.
int main(int AC, char *AV[]) {
// AC: 0-4, AV: the names of WebF, DelF, PasF, StrF; options on which to include and on the translation modes.
// The names of input files for a ‹WEB› file WebF, a ‹Change› file DelF.
// The names of output fules for a «Pas» file PasF and a string pool output StrF.
// Fatal errors do a non-local jump to Exit.
// program TANGLE(WebF, DelF, PasF, StrF);

// Set initial values (3/14) (0x01-0x1f, 0x80-0xff: continued from above).
// Here now is the system-dependent part of the character set.
// If you have, for example, an extended character set like the one in Appendix C of ≪_The «TeX» book_≫,
// the ininitialization of 0x01 ⋯ 0x1f should be changed to
//	for (InChar In = 0x01; In < 0x20; In↑) CharOf[In] = chr(In);
// ‹WEB›'s character set is essentially identical to «TeX»'s, even with respect to characters less than 0x20.

// The following system-independent code makes ByteOf[] contain a suitable inverse to the information in CharOf[].
   for (char Ex = ExCharLo; Ex ≤ ExCharHi; Ex↑) ByteOf[Ex] = ' ';
   for (InChar In = 0x01; In ≤ 0xff; In↑) ByteOf[CharOf[In]] = In;
   ByteOf[' '] = ' ';

// Open the output files PasF and StrF, based on the command-line arguments and options.
   OpenOutput();

// This is the only non-local goto statement in ‹TANGLE›.
// It is used when no recovery from a particular error has been provided.
   if (setjmp(ExitLab)) goto Exit;

// Initialize the input system.
// Open the input file WebF and DelF, based on the command-line arguments and options.
   OpenInput(),
   ExY = CurY = 0;
   InDel = true, PreSetDelBuf(), ToggleDel();
   InEnd = InBuf, InBeg = InBuf + 1, InBuf[0] = ' ', InEnded = false;

   printf(Banner "\n");	// print a ‟banner line”

// Phase I: Read all the user's text and compress it into TokPool[].
   Scanning = true, ModNum = 0;
   do NextTok = SkipAhead(); while (NextTok ≠ NewModCQ);
   while (!InEnded) ScanModule();
// Check that all changes have been read
// At the end of the program, we will tell the user if the change file had a line that didn't match any relevant line in WebF.
   if (DelEnd ≠ InBuf) {	// InDel is false
      for (String InP = InBuf, DelP = DelBuf; InP < DelEnd; InP↑, DelP↑) *InP = *DelP;
      InDel = true, CurY = ExY, InEnd = InBeg = DelEnd;
      Error(Failed, "Change file entry did not match");
   }
   Scanning = false;

// Phase II: Output the contents of the compressed tables.
// To complete the output process, we need a routine that takes the results of GetOutput() and feeds them to SendOut(), SendVal(), or SendSign().
// SendOutput() will be invoked just once, as follows:
   if (MoreP(TokP) ≡ Tok0) Error(Warned, "No output was specified.");
   else {
      printf("\nWriting the output file"), FlushEx();
   // Initialize the output stacks.
   // To get the output process started, we will perform the following initialization steps.
   // We may assume that MoreP(TokP) ≠ Tok0, since it points to the «Pas» text in the first unnamed module that generates code;
   // if there are no such modules, there is nothing to output, and an error message will have been generated before we do any of the initialization.
      QSP = QStack + 1, ComLevel = 0;
      CurId = Str0, CurAs = MoreP(TokP), CurAt = *CurAs, CurEnd = CurAs[1], CurMod = 0;
   // Initialize the output buffer.
   // During the output process, CurY will equal the number of the next line to be output.
      ExQ = MiscQ, ExEnd = ExAt = ExBeg = ExBuf, ExBuf[0] = 0, CurY = 1;
      SendOutput();
   // Empty the last line from the buffer.
      ExAt = ExEnd, ExBeg = ExBuf, FlushBuffer();
      if (ComLevel ≠ 0) Error(Failed, "Program ended at brace level %u", ComLevel);
      printf("\nDone.");
   }
Exit:
   putchar('\n');
   if (StrPEnd > StrP2) {
   // Finish off the string pool file.
      printf("%1d strings written to string pool file.\n", StrPEnd - StrP2);
      fputc('*', StrF);
      for (int ii = 1; ii < 10; ii↑) ExBuf[ii] = StrPoolX%10, StrPoolX /= 10;
      for (int ii = 9; ii > 0; ii↓) fputc(CharOf['0' + ExBuf[ii]], StrF);
      fputc('\n', StrF);
   }
// Here files should be closed if the operating system requires it.
// Print the job Status.
// Some implementations may wish to pass the Status value to the operating system
// so that it can be used to govern whether or not other programs are started.
// Here we simply report the Status to the user.
   switch (Status) {
      case Okayed: printf("(No errors were found.)\n"); break;
      case Warned: printf("(Did you see the warning message above?)\n"); break;
      case Failed: printf("(Pardon me, but I think I spotted something wrong.)\n"); break;
      case Killed: printf("(That was a fatal error, my friend.)\n"); break;
   }
   return EXIT_SUCCESS;
}
