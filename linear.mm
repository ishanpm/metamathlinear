$(
Updated 9/7 - Replaced axiom labels with better names and made theorem labels more consistent
Updated 9/8 - Added some missing proofs and more deduction form proofs
$)

$(
###############################################################################
Hilbert-style axiomatisation of Linear Logic
###############################################################################

This is an implementation of Girard's linear logic based on _Axioms and Models of Linear Logic_ by Wim H. Hesselink.

Thanks to the dual nature of linear logic, many of the operators are redundant. Only the `%`, `&`, `?`, and `~` operators and the units `_|_` and ` ``|`` ` are needed to construct any expression. The only problem is that to write the definitions of the composite operators, the linear biconditional `O-O` is needed, which in turn depends on `~`, `%`, and `&`. Because of this, any proofs that use the composite operators are presented after all the axioms and definitions.

Linear implication is not available in the first section, so inferences will usually be presented in the form ` ( d % a ) /\ ( d % b ) -> ( d % c ) `. This is equivalent to ` ( ! a (X) ! b ) -O c `. This allows proofs to be used with the cut rule.
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

Here the operators `_|_`, `%`, ` ``|`` `, `&`, `?`, and `~` are defined. Later, the duals `1`, `(+)`, `0`, `(X)`, `!` are defined, plus the implication operators `-O`, `O-O`, and the intuitionistic operators `/\`, `\/`, `-.`, `->`, and `<->`.

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
wbot $a wff _|_ $.
$( Par, multiplicative disjunction. In the resource interpretation, this represents resources that are to be used in parallel. $)
wmd $a wff ( a % b ) $.
$( Linear negation. For any statement `a`, `~ a` is its dual. In the resource interpretation, this represents demand for something. Combining `a` and `~ a` yields `_|_`. $)
wneg $a wff ~ a $.

${
    ax-ibot.1 $e |- a $.
    $( Add a `_|_`. Inverse of ~ax-ebot . $)
    ax-ibot $a |- ( _|_ % a ) $.
$}
${
    ax-ebot.1 $e |- ( _|_ % a ) $.
    $( Remove a `_|_`. Inverse of ~ax-ibot . $)
    ax-ebot $a |- a $.
$}
${
    ax-cut.1 $e |- ( a % b ) $.
    ax-cut.2 $e |- ( ~ b % c ) $.
    $( The cut rule is akin to syllogism in classical logic. It allows `~ a % b` to act like an implication, so that an `a` can be removed and traded for a `b`. $)
    ax-cut $a |- ( a % c ) $.
$}

$( The _init_ rule. This innocent-looking rule looks similar to the Law of Excluded Middle in classical logic, but don't be fooled. This allows us to turn any deduction into its dual by simply performing operations on the `~ a` side and flipping it around to get the reverse implication. This is analogous to using modus tollens in classical logic, but it's especially useful in linear logic because it allows each operator to be defined as its dual with all of the deductions negated and backwards. $)
ax-init $a |- ( ~ a % a ) $.
$( `%` is commutative. $)
ax-mdco $a |- ( ~ ( a % b ) % ( b % a ) ) $.
$( `%` is associative. $)
ax-mdas $a |- ( ~ ( ( a % b ) % c ) % ( a % ( b % c ) ) ) $.

${
    cut1.1 $e |- a $.
    cut1.2 $e |- ( ~ a % b ) $.
    $( Modus ponens like inference. $)
    cut1 $p |- b $=
    ( wbot ax-ibot ax-cut ax-ebot ) BEABACFDGH $.
$}
${
    mdco.1 $e |- ( d % ( a % b ) ) $.
    $( `%` is commutative. Deduction form of ~ax-mdco . $)
    mdco $p |- ( d % ( b % a ) ) $=
    ( wmd ax-mdco ax-cut ) CABEBAEDABFG $.
$}
${
    mdcoi.1 $e |- ( a % b ) $.
    $( `%` is commutative. Inference form of ~ax-mdco . $)
    mdcoi $p |- ( b % a ) $=
    ( wmd ax-mdco cut1 ) ABDBADCABEF $.
$}
${
    mdas.1 $e |- ( d % ( ( a % b ) % c ) ) $.
    $( `%` is associative. Deduction form of ~ax-mdas . $)
    mdas $p |- ( d % ( a % ( b % c ) ) ) $=
    ( wmd ax-mdas ax-cut ) DABFCFABCFFEABCGH $.
$}
${
    mdasi.1 $e |- ( ( a % b ) % c ) $.
    $( `%` is associative. Inference form of ~ax-mdas . $)
    mdasi $p |- ( a % ( b % c ) ) $=
    ( wmd ax-mdas cut1 ) ABECEABCEEDABCFG $.
$}
${
    mdasr.1 $e |- ( d % ( a % ( b % c ) ) ) $.
    $( `%` is associative. Reverse of ~ax-mdas . $)
    mdasr $p |- ( d % ( ( a % b ) % c ) ) $=
    ( wmd mdco mdas ) CABFDCABDBCAFDBCADABCFDEGHGHG $.
$}
${
    mdasri.1 $e |- ( a % ( b % c ) ) $.
    $( `%` is associative. Inference form of ~mdasr . $)
    mdasri $p |- ( ( a % b ) % c ) $=
    ( wmd wbot ax-ibot mdasr ax-ebot ) ABECEABCFABCEEDGHI $.
$}
${
    ibotr.1 $e |- a $.
    $( Add a `_|_`, right hand side. See ~ax-ibot . $)
    ibotr $p |- ( a % _|_ ) $=
    ( wbot ax-ibot mdcoi ) CAABDE $.
$}
${
    ebotr.1 $e |- ( a % _|_ ) $.
    $( Remove a `_|_`, right hand side. See ~ax-ebot . $)
    ebotr $p |- a $=
    ( wbot mdcoi ax-ebot ) AACBDE $.
$}
$( Infer `~ _|_` (secretly `1`). $)
nebot $p |- ~ _|_ $=
 ( wbot wneg ax-init ebotr ) ABACD $.
${
    cutneg.1 $e |- ( a % ~ b ) $.
    cutneg.2 $e |- ( b % c ) $.
    $( Negated version of ~ax-cut . $)
    cutneg $p |- ( a % c ) $=
    ( mdcoi wneg ax-cut ) CACBABCEFABGDFHF $.
$}
${
    cutf.1 $e |- ( b % a ) $.
    cutf.2 $e |- ( ~ b % c ) $.
    $( Left-hand version of ~ax-cut . $)
    cutf $p |- ( c % a ) $=
    ( mdcoi ax-cut ) ACABCBADFEGF $.
$}
${
    dni.1 $e |- ( a % b ) $.
    $( Double negation introduction. $)
    dni $p |- ( a % ~ ~ b ) $=
    ( wneg ax-init mdcoi ax-cut ) ABBDZDZCIHHEFG $.
$}
${
    dne.1 $e |- ( a % ~ ~ b ) $.
    $( Double negation elimination. $)
    dne $p |- ( a % b ) $=
    ( wneg ax-init mdcoi dni ax-cut ) ABDZDZBCBJDBIIBBEFGFH $.
$}
${
    dni1.1 $e |- ( a % b ) $.
    $( Double negation introduction, left hand side. $)
    dni1 $p |- ( ~ ~ a % b ) $=
    ( wneg mdcoi dni ) BADDBAABCEFE $.
$}
${
    dne1.1 $e |- ( ~ ~ a % b ) $.
    $( Double negation elimination, left hand side. $)
    dne1 $p |- ( a % b ) $=
    ( wneg mdcoi dne ) BABAADDBCEFE $.
$}
${
    inenebot.1 $e |- a $.
    $( Add a `~ ~ _|_`. See ~ax-ibot . This is useful for dealing with deductions where the antecedent is negated. $)
    inenebot $p |- ( ~ ~ _|_ % a ) $=
    ( wbot ax-ibot dni1 ) CAABDE $.
$}
${
    enenebot.1 $e |- ( ~ ~ _|_ % a ) $.
    $( Remove a `~ ~ _|_`. Inverse of ~inenebot . $)
    enenebot $p |- a $=
    ( wbot dne1 ax-ebot ) ACABDE $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Additives
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

There are two additive binary connectives: `&` and `(+)`. These relate to treating the involved expressions independently. Here we characterize `&`, and ~df-ad will define `(+)` as its dual.
$)

$c `|` & $.

$( Top, the unit of `&`. In the resource interpretation, this represents an unknown collection of objects. $)
wtop $a wff `|` $.
$( With, additive conjunction. In the resource interpretation, this represents a choice between two resources. $)
wac $a wff ( a & b ) $.

$( Anything can turn into ` ``|`` `. $)
ax-top $a |- ( ~ a & `|` ) $.
${
    ax-iac.1 $e |- ( ~ a % b ) $.
    ax-iac.2 $e |- ( ~ a % c ) $.
    $( `&` introduction rule. $)
    ax-iac $a |- ( ~ a % ( b & c ) ) $.
$}
${
    ax-eac1.1 $e |- ( ~ a % ( b & c ) ) $.
    $( `&` elimination rule, left hand side. $)
    ax-eac1 $a |- ( ~ a % b ) $.
$}
${
    ax-eac2.1 $e |- ( ~ a % ( b & c ) ) $.
    $( `&` elimination rule, right hand side. $)
    ax-eac2 $a |- ( ~ a % c ) $.
$}

${
    iac.1 $e |- ( a % b ) $.
    iac.2 $e |- ( a % c ) $.
    $( `&` introduction rule. ~ax-iac has a negation for some reason, this one doesn't. $)
    iac $p |- ( a % ( b & c ) ) $=
    ( wac wneg dni1 ax-iac dne1 ) ABCFAGBCABDHACEHIJ $.
$}
${
    iaci.1 $e |- a $.
    iaci.2 $e |- b $.
    $( `&` introduction rule. Inference form of ~ax-iac . $)
    iaci $p |- ( a & b ) $=
    ( wac wbot ax-ibot iac ax-ebot ) ABEFABACGBDGHI $.
$}
${
    eac1.1 $e |- ( a % ( b & c ) ) $.
    $( `&` elimination rule, left hand side. ~ax-eac1 has a negation for some reason, this one doesn't. $)
    eac1  $p |- ( a % b ) $=
    ( wneg wac dni1 ax-eac1 dne1 ) ABAEBCABCFDGHI $.
$}
${
    eac1i.1 $e |- ( a & b ) $.
    $( `&` elimination rule, left hand side. Inference form of ~ax-eac1 . $)
    eac1i  $p |- a $=
    ( wbot wneg wac inenebot ax-eac1 enenebot ) ADEABABFCGHI $.
$}
${
    eac2.1 $e |- ( a % ( b & c ) ) $.
    $( `&` elimination rule, right hand side. ~ax-eac2 has a negation for some reason, this one doesn't. $)
    eac2  $p |- ( a % c ) $=
    ( wneg wac dni1 ax-eac2 dne1 ) ACAEBCABCFDGHI $.
$}
${
    eac2i.1 $e |- ( a & b ) $.
    $( `&` elimination rule, right hand side. Inference form of ~ax-eac2 . $)
    eac2i  $p |- b $=
    ( wbot wneg wac inenebot ax-eac2 enenebot ) BDEABABFCGHI $.
$}
${
    acco.1 $e |- ( a % ( b & c ) ) $.
    $( `&` is commutative. $)
    acco $p |- ( a % ( c & b ) ) $=
    ( eac2 eac1 iac ) ACBABCDEABCDFG $.
$}
${
    acas.1 $e |- ( a % ( ( b & c ) & d ) ) $.
    $( `&` is associative. $)
    acas $p |- ( a % ( b & ( c & d ) ) ) $=
    ( wac eac1 eac2 iac ) ABCDFABCABCFZDEGZGACDABCKHAJDEHII $.
$}
${
    acasr.1 $e |- ( a % ( b & ( c & d ) ) ) $.
    $( `&` is associative. Reverse of ~acas . $)
    acasr $p |- ( a % ( ( b & c ) & d ) ) $=
    ( wac eac1 eac2 iac ) ABCFDABCABCDFZEGACDABJEHZGIACDKHI $.
$}
${
    dismdac.1 $e |- ( a % ( b % ( c & d ) ) ) $.
    $( `%` distributes over `&`. $)
    dismdac $p |- ( a % ( ( b % c ) & ( b % d ) ) ) $= ? $.
$}
${
    extmdac.1 $e |- ( a % ( ( b % c ) & ( b % d ) ) ) $.
    $( `%` extracts out of `&`. Converse of ~dismdac . $)
    extmdac $p |- ( a % ( b % ( c & d ) ) ) $= ? $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Exponentials
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

There are two exponential connectives: `?` and `!`. These allow expressions to be duplicated and deleted. Here we characterize `?`, and ~df-pe will define `!` as its dual.
$)

$c ? $.

$( "Why not", negative exponential. $)
wne $a wff ? a $.

${
    ax-ipe.1 $e |- ( ~ a % ? b ) $.
    $( Add a `?` (secretly a `!`). Inverse of ~ax-epe . $)
    ax-ipe $a |- ( ~ ? a % ? b ) $.
$}
${
    ax-epe.1 $e |- ( ~ ? a % ? b ) $.
    $( Remove a `?` (secretly a `!`). Inverse of ~ax-ipe . $)
    ax-epe $a |- ( ~ a % ? b ) $.
$}
$( `? a` can be added into any statement. $)
ax-weak $a |- ( ~ _|_ % ? a ) $.
$( `? a` can be contracted. $)
ax-contr $a |- ( ~ ( ? a % ? a ) % ? a ) $.
$( `! 1`. This is needed to let ~ax-ipe and ~ax-epe work on single items. $)
ax-pemc $a |- ~ ? _|_ $.
$( If all the elements of a multiplicative disjunction have `?`, then `?` can be removed from that disjunction. $)
ax-dig $a |- ( ~ ? ( ? a % ? b ) % ( ? a % ? b ) ) $.



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
wlb $a wff ( a O-O b ) $.

$( Definition of linear biconditional. Since the linear implication has not been defined, this is a mouthfull. The good news is, once the properties of the linear biconditional are proven, it will be much easier to express other definitions. See ~dflb for a cleaner form of the definiition. $)

df-lb $a |- ( ( ~ ( a O-O b ) % ( ( ~ a % b ) & ( ~ b % a ) ) ) & ( ~ ( ( ~ a % b ) & ( ~ b % a ) ) % ( a O-O b ) ) ) $.

${
    lb1d.1 $e |- ( a % b ) $.
    lb1d.2 $e |- ( b O-O c ) $.
    $( Forward deduction using `O-O`. $)
    lb1d $p |- ( a % c ) $=
    ( wneg wmd wlb wac df-lb eac1i cut1 ax-cut ) ABCDBFCGZCFBGZBCHZ
      NOIZEPFQGQFPGBCJKLKM $.
$}
${
    lb2d.1 $e |- ( a % c ) $.
    lb2d.2 $e |- ( b O-O c ) $.
    $( Reverse deduction using `O-O`. $)
    lb2d $p |- ( a % b ) $=
    ( wneg wmd wlb wac df-lb eac1i cut1 eac2i ax-cut ) ACBDBFCGZCFB
      GZBCHZOPIZEQFRGRFQGBCJKLMN $.
$}
${
    lb1i.1 $e |- a $.
    lb1i.2 $e |- ( a O-O b ) $.
    $( Forward inference using `O-O`. $)
    lb1i $p |- b $=
    ( wbot ax-ibot lb1d ax-ebot ) BEABACFDGH $.
$}
${
    lb2i.1 $e |- b $.
    lb2i.2 $e |- ( a O-O b ) $.
    $( Reverse inference using `O-O`. $)
    lb2i $p |- a $=
    ( wbot ax-ibot lb2d ax-ebot ) AEABBCFDGH $.
$}

$( Linear implication, defined by ~df-li . $)
wli $a wff ( a -O  b ) $.
$( Definition of linear implication. $)
df-li $a |- ( ( a -O b ) O-O ( ~ a % b ) ) $.

${
    dfli1.1 $e |- ( a % ( b -O c ) ) $.
    $( Convert from linear implication. $)
    dfli1 $p |- ( a % ( ~ b % c ) ) $=
    ( wli wneg wmd df-li lb1d ) ABCEBFCGDBCHI $.
$}
${
    dfli2.1 $e |- ( a % ( ~ b % c ) ) $.
    $( Convert to linear implication. $)
    dfli2 $p |- ( a % ( b -O c ) ) $=
    ( wli wneg wmd df-li lb2d ) ABCEBFCGDBCHI $.
$}
${
    dfli1i.1 $e |- ( b -O c ) $.
    $( Convert from linear implication. $)
    dfli1i $p |- ( ~ b % c ) $=
    ( wneg wmd wbot wli ax-ibot dfli1 ax-ebot ) ADBEFABABGCHIJ $.
$}
${
    dfli2i.1 $e |- ( ~ b % c ) $.
    $( Convert to linear implication. $)
    dfli2i $p |- ( b -O c ) $=
    ( wli wbot wneg wmd ax-ibot dfli2 ax-ebot ) ABDEABAFBGCHIJ $.
$}
${
    mdm2.1 $e |- ( d % ( a % b ) ) $.
    mdm2.2 $e |- ( b -O c ) $.
    $( Par is monotone in its second argument. $)
    mdm2 $p |- ( d % ( a % c ) ) $=
    ( wmd mdasri wli wneg df-li lb1i ax-cut mdasi ) DACDAGBCDABEHBC
      IBJCGFBCKLMN $.
$}
${
    mdm1.1 $e |- ( d % ( a % b ) ) $.
    mdm1.2 $e |- ( a -O c ) $.
    $( Par is monotone in its first argument. $)
    mdm1 $p |- ( d % ( c % b ) ) $=
    ( mdco mdm2 ) BCDBACDABDEGFHG $.
$}
${
    mdm1i.1 $e |- ( a % b ) $.
    mdm1i.2 $e |- ( a -O c ) $.
    $( Par is monotone in its first argument. Inference form of ~mdm1 . $)
    mdm1i $p |- ( c % b ) $=
    ( wmd wbot ax-ibot mdm1 ax-ebot ) CBFABCGABFDHEIJ $.
$}
${
    mdm2i.1 $e |- ( a % b ) $.
    mdm2i.2 $e |- ( b -O c ) $.
    $( Par is monotone in its second argument. Inference form of ~mdm2 . Essentially ~ax-cut using linear implication. $)
    mdm2i $p |- ( a % c ) $=
    ( wmd wbot ax-ibot mdm2 ax-ebot ) ACFABCGABFDHEIJ $.
$}
${
    mdm1s.1 $e |- ( a -O c ) $.
    $( Par is monotone in its first argument. Syllogism form of ~mdm1 . $)
    mdm1s $p |- ( ( a % b ) -O ( c % b ) ) $=
    ( wmd wneg ax-init mdm1 dfli2i ) ABEZCBEABCJFJGDHI $.
$}
${
    mdm2s.1 $e |- ( b -O c ) $.
    $( Par is monotone in its second argument. Syllogism form of ~mdm2 . $)
    mdm2s $p |- ( ( a % b ) -O ( a % c ) ) $=
    ( wmd wneg ax-init mdm2 dfli2i ) ABEZACEABCJFJGDHI $.
$}
${
    syl.1 $e |- ( a -O b ) $.
    syl.2 $e |- ( b -O c ) $.
    $( Syllogism using linear implication. $)
    syl $p |- ( a -O c ) $=
    ( wli wneg wmd df-li lb1i ax-cut lb2i ) ACFAGZCHMBCABFMBHDABIJB
      CFBGCHEBCIJKACIL $.
$}
${
    mp.1 $e |- a $.
    mp.2 $e |- ( a -O b ) $.
    $( Modus ponens like inference using linear implication. $)
    mp $p |- b $=
    ( wbot ax-ibot mdm2i ax-ebot ) BEABACFDGH $.
$}
$( Identity rule for linear implication. Syllogism form of ~ax-init . $)
id $p |- ( a -O a ) $=
 ( wli wneg wmd ax-init df-li lb2i ) AABACADAEAAFG $.

$( Double negation introduction. Syllogism form of ~dni . $)
dnis $p |- ( a -O ~ ~ a ) $=
 ( wneg wli wmd ax-init mdcoi df-li lb2i ) AABZBZCIJDJIIEFAJGH $.
$( Double negation elimination. Syllogism form of ~dne . $)
dnes $p |- ( ~ ~ a -O a ) $=
 ( wneg wli wmd ax-init mdcoi ax-cut df-li lb2i ) ABZBZACKBZADALAJLJAAEF
  LKKEFGFKAHI $.

${
    acm1.1 $e |- ( d % ( a & b ) ) $.
    acm1.2 $e |- ( a -O c ) $.
    $( With is monotone in its first argument. $)
    acm1 $p |- ( d % ( c & b ) ) $=
    ( eac1 mdm2i eac2 iac ) DCBDACDABEGFHDABEIJ $.
$}
${
    acm2.1 $e |- ( d % ( a & b ) ) $.
    acm2.2 $e |- ( b -O c ) $.
    $( With is monotone in its second argument. $)
    acm2 $p |- ( d % ( a & c ) ) $=
    ( acco acm1 ) DCABACDDABEGFHG $.
$}
${
    acm1i.1 $e |- ( a & b ) $.
    acm1i.2 $e |- ( a -O c ) $.
    $( With is monotone in its first argument. Inference form of ~acm1 . $)
    acm1i $p |- ( c & b ) $=
    ( wac wbot ax-ibot acm1 ax-ebot ) CBFABCGABFDHEIJ $.
$}
${
    acm2i.1 $e |- ( a & b )  $.
    acm2i.2 $e |- ( b -O c ) $.
    $( With is monotone in its second argument. Inference form of ~acm2 . $)
    acm2i $p |- ( a & c ) $=
    ( wac wbot ax-ibot acm2 ax-ebot ) ACFABCGABFDHEIJ $.
$}
${
    acm1s.2 $e |- ( a -O c ) $.
    $( With is monotone in its first argument. Syllogism form of ~acm1 . $)
    acm1s $p |- ( ( a & b ) -O ( c & b ) ) $=
    ( wac wneg ax-init acm1 dfli2i ) ABEZCBEABCJFJGDHI $.
$}
${
    acm2s.2 $e |- ( b -O c ) $.
    $( With is monotone in its second argument. Syllogism form of ~acm2 . $)
    acm2s $p |- ( ( a & b ) -O ( a & c ) ) $=
    ( wac wneg ax-init acm2 dfli2i ) ABEZACEABCJFJGDHI $.
$}

$( Extract forward implication from biconditional. Syllogism form of ~ lb1i . $)
lb1s $p |- ( ( a O-O b ) -O ( a -O b ) ) $=
 ( wlb wli wneg wmd wac df-lb eac1i ax-eac1 df-li cut1 eac2i ax-cut
  lb2i ) ABCZABDZDPEZQFRAEBFZQPSBEAFZRSTGZFUAEPFABHIJQESFZSEQFZQSCZUB
  UCGZABKUDEUEFUEEUDFQSHILMNPQKO $.
$( Extract reverse implication from biconditional. Syllogism form of ~ lb2i . $)
lb2s $p |- ( ( a O-O b ) -O ( b -O a ) ) $=
 ( wlb wli wneg wmd wac df-lb eac1i ax-eac2 df-li cut1 ax-cut lb2i ) A
  BCZBADZDOEZPFQBEAFZPOAEBFZRQSRGZFTEOFABHIJPRCZREPFZBAKUAPERFZUBUAEU
  CUBGZFUDEUAFPRHIJLMOPKN $.
${
    lb1.1 $e |- ( a O-O b ) $.
    $( Extract forward implication from biconditional. Alternate form of ~ lb1i . $)
    lb1 $p |- ( a -O b ) $=
    ( wlb wli lb1s mp ) ABDABECABFG $.
$}
${
    lb2.1 $e |- ( a O-O b ) $.
    $( Extract reverse implication from biconditional. Alternate form of ~ lb2i . $)
    lb2 $p |- ( b -O a ) $=
    ( wlb wli lb2s mp ) ABDBAECABFG $.
$}
$( Forward implication of biconditional definition. $)
dflb1s $p |- ( ( a O-O b ) -O ( ( a -O b ) & ( b -O a ) ) ) $=
 ( wlb wli wac lb1s dfli1i lb2s ax-iac dfli2i ) ABCZABDZBADZEKLMKLA
  BFGKMABHGIJ $.
$( Reverse implication of biconditional definition. $)
dflb2s $p |- ( ( ( a -O b ) & ( b -O a ) ) -O ( a O-O b ) ) $= 
( wli wac wneg wmd wlb ax-init dfli1 dfli2i acm1s acm2s df-lb
  eac2i syl ) ABCZBACZDZAEBFZBEAFZDZABGZRSQDUAPQSPSPEABPHIJKSQTQTQEBA
  QHIJLOUAUBUBEUAFUAEUBFABMNJO $.
$( Nicer definition of biconditional. Uses `O-O` and `-O`. $)
dflb $p |- ( ( a O-O b ) O-O ( ( a -O b ) & ( b -O a ) ) ) $=
 ( wlb wli wac dflb1s dflb2s iaci mp ) ABCZABDBADEZDZKJDZEJKCLMABFA
  BGHJKGI $.

${
    licon.1 $e |- ( c % ( a -O b ) ) $.
    $( Contrapositive rule for linear implication. This follows quite neatly from ~df-li . $)
    licon $p |- ( c % ( ~ b -O ~ a ) ) $=
    ( wneg wmd dfli1 mdasri dni mdasi mdco dfli2 ) CBEZAEZNMEZCCNOC
      NFBCNBCABDGHIJKL $.
$}

$c 1 (X) 0 (+) ! $.
$( One, the unit of `(X)`. Defined by ~df-one . $)
wone $a wff 1 $.
$( One is the dual of Bottom. $)
df-one $a |- ( 1 O-O ~ _|_ ) $.
$( Times, multiplicative conjunction. Defined by ~df-mc . $)
wmc $a wff ( a (X) b ) $.
$( Times is the dual of Par. $)
df-mc $a |- ( ( a (X) b ) O-O ~ ( ~ a % ~ b ) ) $.
$( Zero, the unit of `(+)`. Defined by ~df-zero . $)
wzero $a wff 0 $.
$( Zero is the dual of Top. $)
df-zero $a |- ( 0 O-O ~ `|` ) $.
$( Plus, additive disjunction. Defined by ~df-ad . $)
wad $a wff ( a (+) b ) $.
$( Plus is the dual of With. $)
df-ad $a |- ( ( a (+) b ) O-O ~ ( ~ a & ~ b ) ) $.
$( "Of course", positive exponential. Defined by ~df-pe . $)
wpe $a wff ! a $.
$( "Of course" is the dual of "Why not". $)
df-pe $a |- ( ! a O-O ~ ? ~ b ) $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
Intuiionistic logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

There exists a nice conversion between statements in intuitionistic logic to statements in linear logic. Basically, just throw a bunch of `!` exponentials everywhere and you're good to go. Classical logic can then be recovered using the magic of double negatives.

This conversion relies on the fact that all statements on the "top level", meaning all axioms, proofs, and hypotheses, have an implicit `!` as shown by ~ax-ine . The rules of classical and intuitionistic logic dictate that all expressions can be duplicated in this manner, which is accomplished by filling the subexpressions with lots of `!`.
$)

$c /\ \/ -. -> <-> $.
$( Logical conjunction. Defined by ~df-and . $)
wand $a wff ( a /\ b ) $.
$( Definition of `/\`. It's `&` but with some `!` splashed in for good measure. $)
df-and $a |- ( ( a /\ b ) O-O ( ! a & ! b ) ) $.
$( Logical disjunction. Defined by ~df-or . $)
wor $a wff ( a \/ b ) $.
$( Definition of `\/`. It's `(+)` but with some `!` splashed in for good measure. $)
df-or $a |- ( ( a \/ b ) O-O ( ! a (+) ! b ) ) $.
$( Logical negation. Defined by ~df-not . $)
wnot $a wff -. a $.
$( Definition of `-.`. It's `~` but with some `!` splashed in for good measure. $)
df-not $a |- ( -. a O-O ~ ! a ) $.
$( Logical implication. Defined by ~df-im . $)
wim $a wff ( a -> b ) $.
$( Definition of `->`. It's `-O` but with some `!` splashed in for good measure. Note that only `a` needs the exponential. When this statement is used at the top level, this is equivalent to both sides having the exponential. $)
df-im $a |- ( ( a -> b ) O-O ( ! a -> b ) ) $.
$( Logical biconditional. Defined by ~df-bi . $)
wbi $a wff ( a <-> b ) $.
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
