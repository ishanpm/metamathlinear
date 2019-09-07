$(
$c constant $v variable $f floating (typedef)
$e hypothesis $a axiom $p proof
$)

$(
###############################################################################
Hilbert-style axiomatisation of Linear Logic
###############################################################################

This is an implementation of Girard's linear logic based on _Axioms and Models of Linear Logic_ by Wim H. Hesselink.

Thanks to the dual nature of linear logic, many of the operators are redundant. Only the `%`, `&`, `?`, and `~` operators and the units `_|_` and ` ``|`` ` are needed to construct any expression. The only problem is that to write the definitions of the composite operators, the linear biconditional `O-O` is needed, which in turn depends on `~`, `%`, and `&`. Because of this, any proofs that use the composite operators are presented after all the axioms and definitions.

Linear implication is not available in the first section, so inferences will usually be presented in the form ` ( d % a ) /\ ( d % b ) -> ( d % c ) `. This is equivalent to ` ( a & b ) -O c `. This allows proofs to be used with the cut rule.
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
Pre-logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c |- wff $.
$v a b c d p q r s $.
ta $f wff a $.
tb $f wff b $.
tc $f wff c $.
td $f wff d $.
tp $f wff p $.
tq $f wff q $.
tr $f wff r $.
ts $f wff s $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
Basic stuff
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

Here the operators `_|_`, `%`, ` ``|`` `, `&`, `?`, and `~` are defined. Later, the duals `1`, `(+)`, `0`, `(X)`, `!` are defined, plus the implication operators `-O`, `O-O`, `->`.

Due to the way defenitions work in Metamath (i.e. they don't), my first priority is to get the linear biconditional `O-O` working so that it can be used to define the other operators. Unfortunately, the definition of the linear biconditional depends on `%`, `&`, and `~`, so those need to be defined first. Proofs are generally most useful in the syllogism form `a -O b`, so I'll avoid proving stuff here only to prove it again once `-O` is defined.
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Multiplicatives
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

There are two multiplicative binary connectives: `(X)` and `%`. In the resource interpretation, these correspond to treating the resources involved in a parallel manner. Here we characterize `%`, and ~df-mc will define `(X)` as its dual.
$)

$c _|_ % ~ ( ) $.

$( Bottom, the unit of `%`. In the resource interpretation, this represents an impossibility. $)
tbot $a wff _|_ $.
$( Par, multiplicative disjunction. In the resource interpretation, this represents resources that are to be used in parallel. $)
tmd $a wff ( a % b ) $.
$( Linear negation. For any statement `a`, `~ a` is its dual. In the resource interpretation, this represents demand for something. Combining `a` and `~ a` yields `_|_`. $)
tneg $a wff ~ a $.

${
    ax-1a.1 $e |- a $.
    $( Add a `_|_`. Inverse of ~ax-1b . $)
    ax-1a $a |- ( _|_ % a ) $.
$}
${
    ax-1b.1 $e |- ( _|_ % a ) $.
    $( Remove a `_|_`. Inverse of ~ax-1a . $)
    ax-1b $a |- a $.
$}
${
    ax-cut.1 $e |- ( a % b ) $.
    ax-cut.2 $e |- ( ~ b % c ) $.
    $( The cut rule is akin to syllogism in classical logic. It allows `~ a % b` to act like an implication, so that an `a` can be removed and traded for a `b`. $)
    ax-cut $a |- ( a % c ) $.
$}

$( The _init_ rule. $)
ax-2 $a |- ( ~ a % a ) $.
$( `%` is commutative. $)
ax-3 $a |- ( ~ ( a % b ) % ( b % a ) ) $.
$( `%` is associative. $)
ax-4 $a |- ( ~ ( ( a % b ) % c ) % ( a % ( b % c ) ) ) $.

${
    cut1.1 $e |- a $.
    cut1.2 $e |- ( ~ a % b ) $.
    $( Modus ponens like inference. $)
    cut1 $p |- b $=
    ( tbot ax-1a ax-cut ax-1b ) BEABACFDGH $.
$}
${
    a3i.1 $e |- ( a % b ) $.
    $( `%` is commutative. Inference form of ~ax-3 . $)
    a3i $p |- ( b % a ) $=
    ( tmd ax-3 cut1 ) ABDBADCABEF $.
$}
${
    a4i.1 $e |- ( ( a % b ) % c ) $.
    $( `%` is associative. Inference form of ~ax-4 . $)
    a4i $p |- ( a % ( b % c ) ) $=
    ( tmd ax-4 cut1 ) ABECEABCEEDABCFG $.
$}
$( `%` is associative. Reverse of ~ax-4 . $)
a4r $p |- ( ~ ( a % ( b % c ) ) % ( ( a % b ) % c ) ) $=
( tmd tneg ax-3 ax-4 ax-cut ) ABCDZDEZCABDZDZKCDJCADZBDZLJBMDZNJIA
  DOAIFBCAGHBMFHCABGHCKFH $.
${
    a4ri.1 $e |- ( a % ( b % c ) ) $.
    $( `%` is associative. Inference form of ~a4r . $)
    a4ri $p |- ( ( a % b ) % c ) $=
    ( tmd a4r cut1 ) ABCEEABECEDABCFG $.
$}
${
    a1ar.1 $e |- a $.
    $( Add a `_|_`, right hand side. See ~ax-1a . $)
    a1ar $p |- ( a % _|_ ) $=
    ( tbot ax-1a a3i ) CAABDE $.
$}
${
    a1br.1 $e |- ( a % _|_ ) $.
    $( Remove a `_|_`, right hand side. See ~ax-1b . $)
    a1br $p |- a $=
    ( tbot a3i ax-1b ) AACBDE $.
$}
${
    cutneg.1 $e |- ( a % ~ b ) $.
    cutneg.2 $e |- ( b % c ) $.
    $( Negated version of ~ax-cut . $)
    cutneg $p |- ( a % c ) $=
    ( a3i tneg ax-cut ) CACBABCEFABGDFHF $.
$}
${
    cutf.1 $e |- ( b % a ) $.
    cutf.2 $e |- ( ~ b % c ) $.
    $( Left-hand version of ~ax-cut . $)
    cutf $p |- ( c % a ) $=
    ( a3i ax-cut ) ACABCBADFEGF $.
$}
${
    dni.1 $e |- ( a % b ) $.
    $( Double negation introduction. $)
    dni $p |- ( a % ~ ~ b ) $=
    ( tneg ax-2 a3i ax-cut ) ABBDZDZCIHHEFG $.
$}
${
    dne.1 $e |- ( a % ~ ~ b ) $.
    $( Double negation elimination. $)
    dne $p |- ( a % b ) $=
    ( tneg ax-2 a3i dni ax-cut ) ABDZDZBCBJDBIIBBEFGFH $.
$}
${
    a3.1 $e |- ( d % ( a % b ) ) $.
    $( `%` is commutative. Inference form of ~ax-3 . $)
    a3 $p |- ( d % ( b % a ) ) $=
    ( tmd ax-3 ax-cut ) CABEBAEDABFG $.
$}
${
    a4.1 $e |- ( d % ( ( a % b ) % c ) ) $.
    $( `%` is associative. Inference form of ~ax-4 . $)
    a4 $p |- ( d % ( a % ( b % c ) ) ) $=
    ( tmd ax-4 ax-cut ) DABFCFABCFFEABCGH $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Additives
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

There are two additive binary connectives: `&` and `(+)`. These relate to treating the involved expressions independently. Here we characterize `&`, and ~df-ad will define `(+)` as its dual.
$)

$c `|` & $.

$( Top, the unit of `&`. In the resource interpretation, this represents an unknown collection of objects. $)
ttop $a wff `|` $.
$( With, additive conjunction. In the resource interpretation, this represents a choice between two resources. $)
tac $a wff ( a & b ) $.

$( Anything can turn into ` ``|`` `. $)
ax-5 $a |- ( ~ a & `|` ) $.
${
    ax-6.1 $e |- ( ~ a % b ) $.
    ax-6.2 $e |- ( ~ a % c ) $.
    $( `&` introduction rule. $)
    ax-6 $a |- ( ~ a % ( b & c ) ) $.
$}
${
    ax-7a.1 $e |- ( ~ a % ( b & c ) ) $.
    $( `&` elimination rule, left hand side. $)
    ax-7a $a |- ( ~ a % b ) $.
$}
${
    ax-7b.1 $e |- ( ~ a % ( b & c ) ) $.
    $( `&` elimination rule, right hand side. $)
    ax-7b $a |- ( ~ a % c ) $.
$}

${
    a7ai.1 $e |- ( a & b ) $.
    $( `&` elimination rule, left hand side. Inference form of ~ax-7a . $)
    a7ai $p |- a $=
    ( tbot tneg ax-2 a3i tac a1ar ax-cut ax-7a ax-1b ) ADDEZAMDDFGM
      ABABHZMEZNDONCIOMMFGJGKJL $.
$}
${
    a7bi.1 $e |- ( a & b ) $.
    $( `&` elimination rule, right hand side. Inference form of ~ax-7b . $)
    a7bi $p |- b $=
    ( tbot tneg ax-2 a3i tac a1ar ax-cut ax-7b ax-1b ) BDDEZBMDDFGM
      ABABHZMEZNDONCIOMMFGJGKJL $.
$}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Exponentials
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

There are two exponential connectives: `?` and `!`. These allow expressions to be duplicated and deleted. Here we characterize `?`, and ~df-pe will define `!` as its dual.
$)

$c ? $.

$( "Why not", negative exponential. $)
tne $a wff ? a $.

${
    ax-8a.1 $e |- ( ~ a % ? b ) $.
    $( Add a `?` (secretly a `!`). Inverse of ~ax-8b . $)
    ax-8a $a |- ( ~ ? a % ? b ) $.
$}
${
    ax-8b.1 $e |- ( ~ ? a % ? b ) $.
    $( Remove a `?` (secretly a `!`). Inverse of ~ax-8a . $)
    ax-8b $a |- ( ~ a % ? b ) $.
$}
$( `? a` can be added into any statement. $)
ax-9 $a |- ( ~ _|_ % ? a ) $.
$( `? a` can be contracted. $)
ax-10 $a |- ( ~ ( ? a % ? a ) % ? a ) $.
$( `? _|_` can be removed. $)
ax-11 $a |- ~ ? _|_ $.
$( If all the elements of a multiplicative disjunction have `?`, then `?` can be removed from that disjunction. $)
ax-12 $a |- ( ~ ? ( ? a % ? b ) % ( ? a % ? b ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Implication
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Yay, implication!

The linear implication operator `a -O b` reads as, "Given an `a`, I can exchange it for a `b`." This is closely related to the logical implication `->` which can be interpreted as, "Given a proof of `a`, I can prove `b`." The important difference is that the linear implication and the antecedent are both consumed by this action. The linear biconditional can work either way; the choice is given to you by the `&` in its definition.

The linear biconditional is used to write all definitions, except itself (~df-lb ).
$)

$c -O O-O $.

$( Linear biconditional, defined by ~df-lb . This is the operator used for definitions, so its definition will be a little unusual... $)
tlb $a wff ( a O-O b ) $.

$( Definition of linear biconditional. Since the linear implication has not been defined, this is a mouthfull. The good news is, once the properties of the linear biconditional are proven, it will be much easier to express other definitions. $)

df-lb $a |- ( ( ~ ( a O-O b ) % ( ( ~ a % b ) & ( ~ b % a ) ) ) & ( ~ ( ( ~ a % b ) & ( ~ b % a ) ) % ( a O-O b ) ) ) $.

${
    lb1i.1 $e |- a $.
    lb1i.2 $e |- ( a O-O b ) $.
    $( Forward inference using `O-O`. $)
    lb1i $p |- b $=
    ( tneg tmd tlb tac df-lb a7ai cut1 ) ABCAEBFZBEAFZABGZLMHZDNEOF
      OENFABIJKJK $.
$}
${
    lb2i.1 $e |- b $.
    lb2i.2 $e |- ( a O-O b ) $.
    $( Reverse inference using `O-O`. $)
    lb2i $p |- a $=
    ( tneg tmd tlb tac df-lb a7ai cut1 a7bi ) BACAEBFZBEAFZABGZMNHZ
      DOEPFPEOFABIJKLK $.
$}

$( Linear implication, defined by ~df-li . $)
tli $a wff ( a -O  b ) $.
$( Definition of linear implication. $)
df-li $a |- ( ( a -O b ) O-O ( ~ a % b ) ) $.

$( Par is monotone in its first argument. $)
mdm1 $p |- ( ( a -O c ) -O ( ( a % b ) -O ( c % b ) ) ) $= ? $.
$( Par is monotone in its second argument. $)
mdm2 $p |- ( ( b -O c ) -O ( ( a % b ) -O ( a % c ) ) ) $= ? $.
${
    mdm1i.1 $e |- ( a % b ) $.
    mdm1i.2 $e |- ( a -O c ) $.
    $( Par is monotone in its first argument. $)
    mdm1i $p |- ( c % b ) $= ? $.
$}
${
    mdm2i.1 $e |- ( a % b ) $.
    mdm2i.2 $e |- ( b -O c ) $.
    $( Par is monotone in its second argument. Essentially ~ax-cut using linear implication. $)
    mdm2i $p |- ( a % c ) $= ? $.
$}
${
    syl.1 $e |- ( a -O b ) $.
    syl.2 $e |- ( b -O c ) $.
    $( Syllogism using linear implication. $)
    syl $p |- ( a -O c ) $=
    ( tli tneg tmd df-li lb1i mdm2i lb2i ) ACFAGZCHMBCABFMBHDABIJEKA
      CIL $.
$}
${
    mp.1 $e |- a $.
    mp.2 $e |- ( a -O b ) $.
    $( Modus ponens like inference using linear implication. $)
    mp $p |- b $=
    ( tbot ax-1a mdm2i ax-1b ) BEABACFDGH $.
$}
$( Identity rule for linear implication. Syllogism form of ~ax-2 . $)
id $p |- ( a -O a ) $=
 ( tli tneg tmd ax-2 df-li lb2i ) AABACADAEAAFG $.

$( Double negation introduction. Syllogism form of ~dni . $)
dnis $p |- ( a -O ~ ~ a ) $=
 ( tneg tli tmd ax-2 a3i df-li lb2i ) AABZBZCIJDJIIEFAJGH $.
$( Double negation elimination. Syllogism form of ~dne . $)
dnes $p |- ( ~ ~ a -O a ) $=
 ( tneg tli tmd ax-2 a3i ax-cut df-li lb2i ) ABZBZACKBZADALAJLJAAEF
  LKKEFGFKAHI $.

${
    a6alt.1 $e |- ( a % b ) $.
    a6alt.2 $e |- ( a % c ) $.
    $( `&` introduction rule. ~ax-6 has a negated input for some reason, this doesn't. $)
    a6alt $p |- ( a % ( b & c ) ) $=
    ( tneg tac dnis mdm1i ax-6 dnes ) AFZFZBCGALBCABMDAHZIACMENIJAKI
      $.
$}
${
    a7aalt.1 $e |- ( a % ( b & c ) ) $.
    $( `&` elimination rule, left hand side. ~ax-7a has a negated input for some reason, this doesn't. $)
    a7aalt $p |- ( a % b ) $=
    ( tneg tac dnis mdm1i ax-7a dnes ) AEZEZBAKBCABCFLDAGHIAJH $.
$}
${
    a7balt.1 $e |- ( a % ( b & c ) ) $.
    $( `&` elimination rule, right hand side. ~ax-7b has a negated input for some reason, this doesn't. $)
    a7balt $p |- ( a % c ) $=
    ( tneg tac dnis mdm1i ax-7b dnes ) AEZEZCAKBCABCFLDAGHIAJH $.
$}
$( `&` elimination rule, left hand side. Syllogism form of ~ax-7a . $)
a7as $p |- ( ( a & b ) -O a ) $= ? $.
$( `&` elimination rule, right hand side. Syllogism form of ~ax-7b . $)
a7bs $p |- ( ( a & b ) -O b ) $= ? $.
${
    acm1.1 $e |- ( a & b )  $.
    acm1.2 $e |- ( a -O c ) $.
    $( With is monotone in its first argument. $)
    acm1 $p |- ( c & b ) $= ? $.
$}
${
    acm2.1 $e |- ( a & b )  $.
    acm2.2 $e |- ( b -O c ) $.
    $( With is monotone in its second argument. $)
    acm2 $p |- ( a & c ) $= ? $.
$}
$( With is monotone in its first argument. $)
acm1s $p |- ( ( a -O c ) -O ( ( a & b ) -O ( c & b ) ) ) $= ? $.
$( With is monotone in its second argument. $)
acm2s $p |- ( ( b -O c ) -O ( ( a & b ) -O ( a & c ) ) ) $= ? $.

$( Extract forward implication from biconditional. Syllogism form of ~ lb1i . $)
lb1s $p |- ( ( a O-O b ) -O ( a -O b ) ) $=
 ( tlb tli tneg tmd tac df-lb a7ai ax-7a df-li cut1 a7bi ax-cut
  lb2i ) ABCZABDZDPEZQFRAEBFZQPSBEAFZRSTGZFUAEPFABHIJQESFZSEQFZQSCZUB
  UCGZABKUDEUEFUEEUDFQSHILMNPQKO $.
$( Extract reverse implication from biconditional. Syllogism form of ~ lb2i . $)
lb2s $p |- ( ( a O-O b ) -O ( b -O a ) ) $=
 ( tlb tli tneg tmd tac df-lb a7ai ax-7b df-li cut1 ax-cut lb2i ) A
  BCZBADZDOEZPFQBEAFZPOAEBFZRQSRGZFTEOFABHIJPRCZREPFZBAKUAPERFZUBUAEU
  CUBGZFUDEUAFPRHIJLMOPKN $.
${
    lb1.1 $e |- ( a O-O b ) $.
    $( Extract forward implication from biconditional. Alternate form of ~ lb1i . $)
    lb1 $p |- ( a -O b ) $=
    ( tlb tli lb1s mp ) ABDABECABFG $.
$}
${
    lb2.1 $e |- ( a O-O b ) $.
    $( Extract reverse implication from biconditional. Alternate form of ~ lb2i . $)
    lb2 $p |- ( b -O a ) $=
    ( tlb tli lb2s mp ) ABDBAECABFG $.
$}
$( Forward implication of biconditional definition. $)
dflb1 $p |- ( ( a O-O b ) -O ( ( a -O b ) & ( b -O a ) ) ) $=
 ( tlb tli tac tneg tmd lb1s df-li lb1i lb2s ax-6 lb2i ) ABCZABDZBA
  DZEZDNFZQGNOPNODROGABHNOIJNPDRPGABKNPIJLNQIM $.
$( Reverse implication of biconditional definition. $)
dflb2 $p |- ( ( ( a -O b ) & ( b -O a ) ) -O ( a O-O b ) ) $= ? $.
$( Nicer definition of biconditional. Uses `O-O` and `-O`. $)
dflb $p |- ( ( a O-O b ) O-O ( ( a -O b ) & ( b -O a ) ) ) $= ? $.

$( Contrapositive rule for linear implication. This follows quite neatly from ~df-li . $)
licon $p |- ( ( a -O b ) -O ( ~ b -O ~ a ) ) $= ? $.

$c 1 (X) 0 (+) ! $.
$( One, the unit of `(X)`. Defined by ~df-one . $)
tone $a wff 1 $.
$( One is the dual of Bottom. $)
df-one $a |- ( 1 O-O ~ _|_ ) $.
$( Times, multiplicative conjunction. Defined by ~df-mc . $)
tmc $a wff ( a (X) b ) $.
$( Times is the dual of Par. $)
df-mc $a |- ( ( a (X) b ) O-O ~ ( ~ a % ~ b ) ) $.
$( Zero, the unit of `(+)`. Defined by ~df-zero . $)
tzero $a wff 0 $.
$( Zero is the dual of Top. $)
df-zero $a |- ( 0 O-O ~ `|` ) $.
$( Plus, additive disjunction. Defined by ~df-ad . $)
tad $a wff ( a (+) b ) $.
$( Plus is the dual of With. $)
df-ad $a |- ( ( a (+) b ) O-O ~ ( ~ a & ~ b ) ) $.
$( "Of course", positive exponential. Defined by ~df-pe . $)
tpe $a wff ! a $.
$( "Of course" is the dual of "Why not". $)
df-pe $a |- ( ! a O-O ~ ? ~ b ) $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
Intuiionistic logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

There exists a nice conversion between statements in intuitionistic logic to statements in linear logic. Basically, just throw a bunch of `!` exponentials everywhere and you're good to go. Classical logic can then be recovered using the magic of double negatives.

This conversion relies on the fact that all statements on the "top level", meaning all axioms, proofs, and hypotheses, have an implicit `!` as shown by ~ax-8a . The rules of classical and intuitionistic logic dictate that all expressions can be duplicated in this manner, which is accomplished by filling the subexpressions with lots of `!`.
$)

$c /\ \/ -. -> <-> $.
$( Logical conjunction. Defined by ~df-and . $)
tand $a wff ( a /\ b ) $.
$( Definition of `/\`. It's `&` but with some `!` splashed in for good measure. $)
df-and $a |- ( ( a /\ b ) O-O ( ! a & ! b ) ) $.
$( Logical disjunction. Defined by ~df-or . $)
tor $a wff ( a \/ b ) $.
$( Definition of `\/`. It's `(+)` but with some `!` splashed in for good measure. $)
df-or $a |- ( ( a \/ b ) O-O ( ! a (+) ! b ) ) $.
$( Logical negation. Defined by ~df-not . $)
tnot $a wff -. a $.
$( Definition of `-.`. It's `~` but with some `!` splashed in for good measure. $)
df-not $a |- ( -. a O-O ~ ! a ) $.
$( Logical implication. Defined by ~df-im . $)
tim $a wff ( a -> b ) $.
$( Definition of `->`. It's `-O` but with some `!` splashed in for good measure. Note that only `a` needs the exponential. When this statement is used at the top level, this is equivalent to both sides having the exponential. $)
df-im $a |- ( ( a -> b ) O-O ( ! a -> b ) ) $.
$( Logical biconditional. Defined by ~df-bi . $)
tbi $a wff ( a <-> b ) $.
$( Definition of `<->`, in terms of the other logical connectives. $)
df-bi $a |- ( ( a <-> b ) O-O ( ( a -> b ) /\ ( b -> a ) ) ) $.

$( $t
htmldef "|-"  as "<span style='color:gray;'>&#x22a6;</span> ";
htmldef "wff" as "<span style='color:gray;'>wff</span> ";
htmldef "("   as "( ";
htmldef ")"   as ") ";
htmldef "1"   as "1 ";
htmldef "_|_" as "&#x22a5; ";
htmldef "(X)" as "&otimes; ";
htmldef "%"   as "&#x214b; ";
htmldef "~"   as "~ ";
htmldef "-O"  as "&#x22b8; ";
htmldef "O-O" as "&#x29df; ";
htmldef "`|`" as "&#x22a4; ";
htmldef "0"   as "0 ";
htmldef "&"   as "&amp; ";
htmldef "(+)" as "&oplus; ";
htmldef "?"   as "? ";
htmldef "!"   as "! ";
htmldef "->"  as "&rarr; ";
htmldef "<->" as "&harr; ";
htmldef "/\"  as "&and; ";
htmldef "\/"  as "&or; ";
htmldef "-."  as "&not; ";
htmldef "a"   as "<span style='color:blue;'>a</span> ";
htmldef "b"   as "<span style='color:blue;'>b</span> ";
htmldef "c"   as "<span style='color:blue;'>c</span> ";
htmldef "d"   as "<span style='color:blue;'>d</span> ";
htmldef "p"   as "<span style='color:blue;'>p</span> ";
htmldef "q"   as "<span style='color:blue;'>q</span> ";
htmldef "r"   as "<span style='color:blue;'>r</span> ";
htmldef "s"   as "<span style='color:blue;'>s</span> ";
$)
