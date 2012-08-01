\documentclass{jfp1}
\usepackage{amsfonts}
\usepackage{stmaryrd}
\usepackage{upgreek}
\usepackage{url}


\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}

\ColourStuff

\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\C}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\purple{\mathit{#1}}}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% CODE PREAMBLE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%if False
\begin{code}
{-# OPTIONS --universe-polymorphism #-}

module LitOrn where

data Level : Set where
  zl : Level
  sl : Level -> Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO zl #-}
{-# BUILTIN LEVELSUC sl #-}

_o_ :  forall {a b c}
       {R : Set a} {S : R -> Set b} {T : (r : R) -> S r -> Set c} ->
       (forall {r} (s : S r) -> T r s) -> (g : (r : R) -> S r) →
       ((r : R) → T r (g r))
f o g = \ r -> f (g r)
infixl 5 _o_

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst

open Sg public
infixr 4 _,_


_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T

un : forall {a}{S T}{P : Sg S T -> Set a} ->
      ((s : S)(t : T s) -> P (s , t)) ->
      (st : Sg S T) -> P st
un = \ p st -> p (fst st) (snd st)

cu :  forall {a}{S T}{P : Sg S T -> Set a}
      -> ((st : Sg S T) -> P st)
      -> (s : S)(t : T s) -> P (s , t)
cu p s t = p (s , t)


id : forall {a} {A : Set a} -> A -> A
id x = x

nip_gap : forall {a} {A : Set a} -> A -> A
nip x gap = x



data ANat : Set where
  zeroA  : ANat
  sucA   : ANat -> ANat

_+A_ : ANat -> ANat -> ANat
zeroA +A n = n
sucA m +A n = sucA (m +A n)

record One : Set where
  constructor <>

! : forall {J : Set} -> J -> One
! _ = _

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

_//_ : forall {X Y : Set}(f : X -> Y){x x' : X} -> x == x' -> f x == f x'
f // refl = refl

infixr 4 _-:>_

infixr 5 _::_

\end{code}
%endif
\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}

%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"
%format nip = "\!"
%format gap = "\quad"
%format constructor = "\mathkw{constructor}"
%format -> = "\blue{\rightarrow}"
%format Sg = "\blue{\Upsigma}"
%format One = "\blue{1}"
%format \ = "\red{\lambda}"
%format <> = "\red{\langle\rangle}"
%format , = "\red{,}\,"
%format == = "\D{=\!\!=}"
%format refl = "\C{refl}"
%format ANat = "\D{Nat}"
%format zeroA = "\C{zero}"
%format sucA = "\C{suc}"
%format ! = "\F{!}"
%format o = "\F{\cdot}"
%format fst = "\F{fst}"
%format snd = "\F{snd}"
%format un = "\T{V}\!"
%format cu = "\T{\(\Lambda\)}\!"
%format // = "\T{\(\green{\parallel}\)}"
%format +A = "\mathbin{\F{+}}"

\newtheorem{proposition}{Proposition}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Title
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\title{Ornamental Algebras, Algebraic Ornaments}
\author[Conor McBride]{CONOR McBRIDE\\
Department of Computer and Information Sciences \\
University of Strathclyde\\ Glasgow, Scotland\\
\email{conor@@cis.strath.ac.uk}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{document}
\label{firstpage}
\maketitle
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% ABSTRACT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{abstract}
  This paper re-examines the presentation of datatypes in dependently
  typed languages, addressing in particular the issue of what it means
  for one datatype to be in various ways more informative than
  another.  Informal human observations like `lists are natural
  numbers with extra decoration' and `vectors are lists indexed by
  length' are expressed in a first class language of \emph{ornaments}
  --- presentations of fancy new types based on plain old ones ---
  encompassing both decoration and, in the sense of Tim Freeman and
  Frank Pfenning~\shortcite{freeman.pfenning:refinementML},
  refinement.

  Each ornament adds information, so it comes with a forgetful
  function from fancy data back to plain, expressible as the fold of its
  \emph{ornamental algebra}: lists built from numbers acquire the `length'
  algebra. Conversely, each algebra for a datatype induces a way to
  index it --- an \emph{algebraic ornament}. The length algebra for lists
  induces the construction of the paradigmatic dependent vector types.

  Dependent types thus provide not only a new `axis of diversity' ---
  indexing --- for data structures, but also new abstractions to
  manage and exploit that diversity. In the spirit of `the new
  programming'~\cite{conor.james:viewfromleft}, the engineering of
  coincidence is replaced by the propagation of consequence.
\end{abstract}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%format Set = "\D{Set}"
%format Vec = "\D{Vec}"
%format List = "\D{List}"
%format * = "\F{\times}"
%format nil = "\C{[]}"
%format :: = "\C{::}"
%format _::_ = "\_" :: "\_"
%format zip0 = "\F{zip}"
%format zip1 = "\F{zip}"
%format forall = "\D{\forall}"
%format !! = "\!\!\!\yellowBG{!~!}\!\!\!"
%format vecList = "\F{vecList}"
%format listVec = "\F{listVec}"
%format what = "\F{f}"
%format length = "\F{length}"

If it is not a peculiar question, where do datatypes come from? Most
programming languages allow us to \emph{declare} datatypes --- that is
to say, datatypes come from \emph{thin air}. Programs involving the
data thus invented subsequently become admissible, and if we are
fortunate, we may find that some of these programs are amongst those
that we happen to want. What a remarkable coincidence!

In dependently typed programming languages, the possible variations
of datatypes are still more dense and subtle, and the coincidences
all the more astonishing. For example, working in Agda~\cite{norell:agda},
if I have list types, declared thus,
\begin{code}
data List (X : Set) : Set where
  nil   :                 List X
  _::_  : X -> List X ->  List X
\end{code}
I might seek to define |zip0|, the function which rearranges a pair of
lists into a list of pairs. Inevitably, I will face the question of
what to do in the `off-diagonal' cases, where one list is shorter than
the other.
\begin{spec}
zip0 : forall {X Y} -> List X -> List Y -> List (X * Y)
zip0 nil         nil        = nil
zip0 nil         (y :: ys)  = ?
zip0 (x :: xs)   nil        = ?
zip0 (x :: xs)   (y :: ys)  = (x , y) :: zip0 xs ys
\end{spec}
One possibility is to return a \emph{dummy} value, perhaps |nil|, as
in the Haskell standard Prelude~\cite{haskell:prelude}. However, this
practice can often mask the presence of a bug: indeed, I found such a
bug in an early version of Agda.
Such cautionary tales might prompt me to declare \emph{vectors} instead.
\begin{code}
data Vec (X : Set) : ANat -> Set where
  nil   :                                Vec X zeroA
  _::_  : X -> forall {n} -> Vec X n ->  Vec X (sucA n)
\end{code}
As it happens, simple unification constraints on indices rule out the
error cases and allow us stronger guarantees about the valid cases:
\begin{code}
zip1 : forall {X Y n} -> Vec X n -> Vec Y n -> Vec (X * Y) n
zip1 nil         nil        = nil
zip1 (x :: xs)   (y :: ys)  = (x , y) :: zip1 xs ys
\end{code}

These vectors may look a little strange, but perhaps they are in some
way related to lists. Do you think it might be so?
Could we perhaps write functions to convert between the two
\begin{spec}
vecList  : forall {X n} ->  Vec X n        -> List X           -- forgets index
listVec  : forall {X n} ->  (xs : List X)  -> Vec X (what xs)  -- recomputes index with |what|
\end{spec}
for a suitable |what : forall {X} -> List X -> ANat|?
What might |what| be? I know a function in the library with the
right type: perhaps |length| will do.

But I am being deliberately obtuse. Let us rather be acute. These
vectors were conceived as a fancy version of lists, so we should not
be surprised that there is a forgetful function which discards the
additional indexing.  Further, the purpose of indexing vectors is to
expose length in types, so it is not a surprise that this index can be
computed by the |length| function. Indeed, it took an act
self-censorship not to introduce vectors to you in prose, `Vectors are
lists indexed by their length.', but rather just to declare them to
you, as I might to a computer.

In this paper, I show how one might express this prose introduction to
a computer, \emph{constructing} the vectors from the definition of
|length| in such a way as to guarantee their relationship with
lists. The key is to make the definitions of datatypes first-class
citizens of the programming language by establishing a datatype of
datatype descriptions --- a \emph{universe}, in the sense of
Per Martin-L\"of~\shortcite{martinloef:intuitionistic}. This gives us an
effective means to frame the question of what it is for one datatype
to be a `fancy version' of another.

I shall introduce the notion of an \emph{ornament} on a datatype,
combining refinement of indexing and annotation with additional
data. Ornaments, too, are first-class citizens --- we can and will
compute them systematically.  This technology allows us not only to
express vectors as an ornament on lists, but lists themselves as an
ornament on numbers. Moreover, the former can be seen as a consequence
of the latter.

The work I present here is an initial experiment with ornaments,
conducted in Agda, but with the intention of delivering new
functionality for Epigram~\cite{conor.james:viewfromleft}, where the native notion of datatype is now
delivered via a
universe~\cite{chapman.dagand.mcbride.morris:levitation}.  It is
ironic that an Agda formalisation of ornaments is no use for
programming with Agda's native datatypes, good only for those
datatypes within the formal universe. It is this distinction between
the native data and their formal forgeries which must be abolished if
this technology is to achieve its potential, and in the rudimentary
Epigram prototype, it has been. Here, however, I am happy to exploit
the more polished syntax of Agda to assist in the exposition of the
basic idea. The literate Agda source for this paper is available at
\url{http://personal.cis.strath.ac.uk/~conor/pub/OAAO/LitOrn.lagda}.


\subsection*{Related Work}

There is a rich literature on \emph{refinement} types, initially
conceived by Tim Freeman and Frank
Pfenning~\shortcite{freeman.pfenning:refinementML} as a kind of
`logical superstructure' for ML datatypes, and extensively pursued by
Frank Pfenning and his students. Refinement types are at the heart of
Hongwei Xi's design for Dependent ML~\cite{xi.pfenning:dependentML}:
programs are checked at advanced types guaranteeing safety properties,
then erased to Standard ML for execution. Rowan
Davies~\shortcite{davies-05} and Joshua
Dunfield~\shortcite{DunfieldThesis} further study types and type
checking in this setting where the computational substrate is without
dependent types.

More recently, William Lovas and Frank
Pfenning~\shortcite{lovas.pfenning:refinementLF} have adapted the
notion to the Logical Framework, allowing the construction of subset
types with proof irrelevance. Matthieu Sozeau~\shortcite{sozeau:thesis} gives a
treatment of programming with subset types for a proof-irrelevant
incarnation of Coq which has not entirely materialised.

I profit from the insights of the refinement type literature, but in a
more general setting --- full dependent types with proof-irrelevant
propositions~\cite{obseqnow} --- and with greater
fluidity. Refinements are one kind of ornament, but here we shall see
that decoration with additional non-logical data fits in the same
scheme. It becomes interesting to condsider the erasure functions
which ornaments induce as helpful first-class functions, programmed
for free, not just as the erasure preceding execution. We shall surely
want to work with both lists and vectors, for example, but without the
need to spend effort establishing the connection between them.

Literally and metaphorically closer to home, my Strathclyde colleagues
Robert Atkey, Neil Ghani and Patricia
Johann~\shortcite{atkey.ghani.johann:inductiverefinement} have
recently made a study of type refinements induced by algebras over a
datatype's structure --- the \emph{algebraic} ornaments of this
paper's title --- citing an early draft of this paper amongst their
motivation. Their paper gives a crisp and enlightening categorical
account of the broad semantic structure of algebraic ornaments via
fibrations, abstracting away from the details of a particular universe
encoding. I compliment and complement their work, giving a concrete
implementation, and showing how algebras arise \emph{from} ornaments
in my more general decoration-and-refinement sense.


\subsection*{Acknowledgements}

This work was funded in part by EPSRC grant EP/G034699/1
\emph{Reusability and Dependent Types}, whose prospectus derives in part
from my first talk on ornaments, at a Dependently Typed Programming
workshop in February 2008. I am grateful to be a coinvestigator on
this project, and I should like to thank the project team --- Thorsten
Altenkirch, Pierre-\'Evariste Dagand, Neil Ghani, Jeremy Gibbons, Josh
Ko and Peter Morris --- for highly productive discussions. I must also
thank the members of IFIP Working Group 2.1 for helpful feedback on
a presentation of this work. I am delighted also that the
Mathematically Structured Programming group at Strathclyde ---
including Neil and Pierre-\'Evariste, and also Robert Atkey and
Patricia Johann --- has provided such a fertile environment in which
to develop this work. James McKinna, insightful as ever, provoked the
example at the end of the paper: my thanks go also to him.

Technological gratitude is deserved in generous measure by Andres
L\"oh, for his peerless \texttt{lhs2TeX} literate programming system
(now adapted to Agda), and, of course, to Ulf Norell for the Agda
system itself. In a time when research output metrics can so easily
lose sight of the very software artefacts which keep us in business,
we must stand up and give the credit due.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Describing Datatypes}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%format Set1 = "\D{Set1}"
%format PDesc = "\D{Desc}"
%format end = "\C{end}"
%format sg = "\C{\upsigma}"
%format node* = "\C{node\times}"
%format node*_ = node* "\_"
%format ze = "\C{ze}"
%format su = "\C{su}"
%format ZorS = "\D{[ze,su]}"
%format ze-> = "\F{\mathsf{ze}\!\mapsto}"
%format su-> = "\F{\mathsf{su}\!\mapsto}"
%format ze->_su->_ = ze-> "\_" su-> "\_"
%format NatP = "\F{NatP}"
%format <! = "\F{\llbracket}"
%format !>P = "\F{\rrbracket}"
%format <!_!>P = <! "\_" !>P
%format fazzi = z "\;\;"
%format PData = "\D{Data}"
%format << = "\C{\langle}"
%format >> = "\C{\rangle}"
%format <<_>> = << "\_" >>
%format PlainNat = "\F{Nat}"
%format zeroP = "\F{zero}"
%format sucP = "\F{suc}"

In order to manipulate inductive (tree-like) datatypes, we shall need
to represent their \emph{descriptions} as data, then interpret those
descriptions as types.  That is, we must construct what Per Martin-L\"of
calls a \emph{universe}~\cite{martinloef:intuitionistic}. The
techniques involved here are certainly not new: Marcin Benke, Peter
Dybjer and Patrik Jansson~\shortcite{benke.dybjer.jansson:universes}
provide a helpful survey. Here, I follow the recipe from Peter Dybjer
and Anton Setzer's coding of
induction-recursion~\cite{dybjer.setzer:finiteaxiomatization},
suitably adapted to the present purpose.

\subsection{Unindexed inductive datatypes}

Let us start with plain unindexed first-order data
structures, just to get the idea.  You can interpret a plain
|PDesc|ription as a format, or a program for reading a record
corresponding to one node of a tree-like data structure.
\begin{code}
data PDesc : Set1 where
  end     :                               PDesc   -- end of node
  sg      : (S : Set) -> (S -> PDesc) ->  PDesc   -- dependent pair
  node*_  : PDesc ->                      PDesc   -- subnode, then more
\end{code}
The description runs left-to-right, with |end| signalling the end of
the node, |sg S D| indicating an element |s : S| followed by the rest
described by |D s|, and |node* D| marking a place for a subnode
followed by more data described by |D|.

An imaginary Robert Harper reminds me to remark that the use of
functions to account for type dependency in the |sg| constructor does
not constitute `higher-order abstract syntax' in the sense of the
Logical Framework~\cite{hhp:lf}. In terms of
\emph{polarity}~\cite{danNoamBob}, the `positive' LF function space is
restricted to correspond exactly to variable binding, but here I use
the full `negative' function space which allows actual computation,
admitting the so-called `exotic terms' which destroy the
crucial adequacy property of HOAS representations. This choice is
quite deliberate on my part: I make essential use of that extra
computational power, as I shall shortly demonstrate.

Let us have an example description: if we have a two element
enumeration to act as a set of tags, we may describe the natural
numbers. I name the enumeration |ZorS|, a suggestive identifier,
and I exploit Agda's mixfix notation to give a convenient case
analysis operator, especially suited to partial application.
\begin{code}
data ZorS : Set where ze su : ZorS

ze->_su->_ :  forall{a} -> {P : ZorS -> Set a} -> P ze -> P su -> (c : ZorS) -> P c
(ze-> fazzi su-> s)  ze  = fazzi
(ze-> fazzi su-> s)  su  = s
\end{code}
Ulf Norell's~\shortcite{ulf:thesis} rationalisation of Randy
Pollack's~\shortcite{pollack:implicit} \emph{argument synthesis}
incorporates Dale Miller's~\shortcite{miller:mixed} \emph{pattern
  unification}, which will infer a suitably dependent |P| just when
case analysis is \emph{not} fully applied to a scrutinee.

Now we can use the fully computational dependency built into the |sg|
construct to treat `constructor choice' as just another
component of a variant record.
\begin{code}
NatP : PDesc
NatP = sg nip ZorS gap (ze-> nip end gap    su->  node* end)
\end{code}
What does this say? A natural number node begins with a choice of tag;
if the tag is |ze|, we have reached the end; if the tag is |su|, we
require one `predecessor' subnode, then end.

We shall need to interpret descriptions as
actual types in a way which corresponds to the explanation above.
To do so, we may follow the standard construction of an inductive
datatype as the initial algebra of an endofunctor on |Set| which
drives the \emph{algebra of programming} view of data and
functions~\cite{bird97algebra}.
If we have a set |X| representing subnodes, we can give the set
representing whole nodes as follows.
\begin{code}
<!_!>P : PDesc -> Set -> Set
<! end      !>P  X = One
<! sg S D   !>P  X = Sg S \ s -> <! D s !>P X
<! node* D  !>P  X = X * <! D !>P X
\end{code}
Here, |One| is the unit type, with sole inhabitant |<>| and |Sg S T|
is the type of dependent pairs |s , t| (unparenthesized) such
that |s : S| and |t : T s|.
Agda extends the scope of a |\| rightwards as far as possible, reducing
the need for parentheses. Note that |S * T| is defined to be the
non-dependent special case |Sg S \ _ -> T|.

Correspondingly, if |ANat| were the type of natural numbers, we
should have
\begin{spec}
<! NatP !>P ANat = Sg nip ZorS gap (ze-> nip One gap su-> ANat * One )
\end{spec}
But how can we define such a |ANat|, given |NatP|?
This |<!_!>P| interprets a description as a strictly
positive operator on sets, so we are indeed entitled to an inductive
datatype |PData D|, taking a fixpoint, instantiating |X| with
|PData D| itself.
\begin{code}
data PData (D : PDesc) : Set where
  <<_>> : <! D !>P (PData D) -> PData D
\end{code}

We may thus define the set of natural numbers, and its constructors.\\
\parbox{1.5in}{
\begin{code}
PlainNat : Set
PlainNat = PData NatP
\end{code}
}\parbox{1.3in}{
\begin{code}
zeroP : PlainNat
zeroP = << ze , <> >>
\end{code}
}\parbox{1.3in}{
\begin{code}
sucP : PlainNat -> PlainNat
sucP n = << su , n , <> >>
\end{code}}

Sadly, Agda will not let us use these definitions in pattern matching,
so we shall be forced to face artefacts of encoding as we work.
Encoded datatypes make William Aitken and John
Reppy's~\shortcite{aitken.reppy} proposed notion of definition fit for
left and right still more overdue.

We could go on to develop the initial algebra semantics for this
class of functors, but let us first generalise to the indexed case.


\subsection{Indexed inductive types}

%format Desc = "\D{Desc}"
%format say = "\C{say}"
%format ask = "\C{ask}"
%format ** = "\C{*}"
%format ask_**_ = ask "\_" ** "\_"
%format !> = "\F{\rrbracket}"
%format <!_!> = <! "\_" !>
%format Data = "\D{Data}"
%format NatD = "\F{NatD}"
%format Nat = "\F{Nat}"
%format zero = "\F{zero}"
%format suc = "\F{suc}"
%format VecDK = "\F{VecD}"
%format VecK = "\F{Vec}"
%format nilK = "\F{[]}"
%format :K: = "\F{::}"
%format _:K:_ = "\_" :K: "\_"

We can give a type which describes inductively defined families of
datatypes in |I -> Set|~\cite{dybjer:families}. Vectors, parametrized
by their element type but indexed by their length, are a typical example.
Let us revisit them and examine theor salient features.
\[\begin{array}{l}
\begin{array}{c@@{\;}c@@{\;}c@@{\;}c@@{\;}c}
  & \textrm{\scriptsize parameter} && \textrm{\scriptsize index set} \\
           & \downarrow && \downarrow & \\
|data Vec| & \framebox{|(X : Set)|} & |:| & \framebox{|ANat|} & |-> Set where| \\
\end{array}\\
\quad
\begin{array}{||l||@@{\;}l@@{\;}c@@{\;}r@@{\;}||l||}
\cline{1-1} \cline{5-5}
  |nil|  & |:|                          &&    |Vec X| & |zeroA| \\
  |_::_| & |: X -> forall {n} -> Vec X| & \framebox{|n|} & |->  Vec X| & |(sucA n)| \\
\cline{1-1} \cline{5-5}
\multicolumn{1}{c}{\uparrow} & & \uparrow &\multicolumn{1}{r}{}&
 \multicolumn{1}{l}{\uparrow} \\
\multicolumn{1}{c}{\hspace*{ -0.5in}\textrm{\scriptsize constructor choice}\hspace*{ -0.5in}} &
\multicolumn{2}{r}{\textrm{\scriptsize subnode index}} &
\multicolumn{1}{r}{}&
\multicolumn{1}{l}{\textrm{\scriptsize node index}\hspace*{ -0.5in}} \\
\end{array}
\end{array}\]

All that changes is
that we must ask for
a specific index anytime we need a subnode, and we must say which
index we deliver when we reach the end of a node. Let us
adapt our coding system to account for these extra details.
\begin{code}
data Desc (I : Set) : Set1 where
  say      : I ->                           Desc I
  sg       : (S : Set)(D : S -> Desc I) ->  Desc I
  ask_**_  : I -> Desc I ->                 Desc I
\end{code}
Accordingly, the description of vectors is as follows:
\begin{spec}
VecDK : Set -> Desc Nat
VecDK X = sg ZorS (
  ze->                                     say zero
  su-> sg X \ x -> sg Nat \ n -> ask n **  say (suc n) )
\end{spec}

We interpret descriptions again as strictly positive endofunctors,
but this time on |I -> Set|. We are given the indexed family of
recursive subnodes |X : I -> Set|, and we must deliver an indexed family
of nodes in |I ->
Set|. In effect we are told the index which the node must
|say|. Hence, we should interpret the |say| construct with an equality
constraint: |i' == i|, here, is the usual intensional equality type,
allowing constructor |refl| whenever |i'| is definitionally equal to |i|.
When the description |ask|s, we know at which index to
invoke |X|. The treatment of |sg| is just as before.
\begin{code}
<!_!> : forall {I} -> Desc I -> (I -> Set) -> (I -> Set)
<! say i'       !> X i = i' == i
<! sg S D       !> X i = Sg S \ s -> <! D s !> X i
<! ask i' ** D  !> X i = X i' * <! D !> X i
\end{code}
Of course, we acquire inductive datatypes by taking the least
fixpoint.
\begin{code}
data Data {I : Set}(D : Desc I)(i : I) : Set where
  <<_>> : <! D !> (Data D) i -> Data D i
\end{code}
Unindexed datatypes like |Nat| still fit in this picture,
just indexing with |One| and inserting
trivial indices where required:
\begin{code}
NatD : Desc One
NatD = sg nip ZorS gap (ze-> nip say <> gap su-> ask <> **  say <> )
\end{code}
The corresponding type and value constructors acquire trivial
indices and proofs.\\
\parbox{1.5in}{
\begin{code}
Nat : Set
Nat = Data NatD <>
\end{code}}
\parbox{1.3in}{
\begin{code}
zero : Nat
zero = << ze , refl >>
\end{code}}
\parbox{1.3in}{
\begin{code}
suc : Nat -> Nat
suc n = << su , n , refl >>
\end{code}}

However, we are now in a position to implement the type and value
constructors for nontrivially indexed structures, like the vectors:
%if False
\begin{code}
VecDK : Set -> Desc Nat
VecDK X = sg ZorS (
  ze->                                     say zero
  su-> sg X \ x -> sg Nat \ n -> ask n **  say (suc n) )
\end{code}
%endif
\begin{code}
VecK : Set -> Nat -> Set
VecK X n = Data (VecDK X) n

nilK : forall {X} -> VecK X zero
nilK = << ze , refl >>

_:K:_ : forall {X} -> X -> forall {n} -> VecK X n -> VecK X (suc n)
_:K:_ x {n} xs = << su , x , n , xs , refl >>
\end{code}

There are many ways to go about the encoding of inductive families.
This choice is rather limited in that it does not allow infinitely
branching recursion, and rather rigid in that it prevents us from
using the node index \emph{a priori} to compute the node structure.
There is no barrier in principle to adapting the techniques of this
paper for more sophisticated
encodings~\cite{chapman.dagand.mcbride.morris:levitation}, but there
is, I hope, a pedagogical benefit in choosing an encoding which
corresponds straightforwardly and faithfully to the more familiar mode
of defining inductive families in type theory or the `Generalized
Algebraic Data Types' now popular in
Haskell~\cite{cheney:gadt,xi:gadt,sheard:gadt,spj:gadt}.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Map and Fold with Indexed Algebras}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%format MU = "\blue{\upmu}"
%format cin = "\C{in}"
%format map = "\F{map}"
%format mapF = map "_{" F "}"
%format fold = "\F{fold}"
%format foldF = fold "_{" F "}"
%format phi = "\V{\phi}"
%format -:> = "\F{\;\::\!\!\!\!\!\to}"
%format _-:>_ = "\_" -:> "\_"
%format mapFold = "\F{mapFold}"
%format foold = fold
\newcommand{\T}[1]{\raisebox{0.02in}{\tiny\green{\textsc{#1}}}}
%format kc = "\T{K}\!"
%format addA = "\F{addA}"
%format concatA = "\F{concatA}"
%format + = "\F{+}"
%format _+_ = "\_" + "\_"
%format +K+ = "\F{+\!+}"
%format _+K+_ = "\_" +K+ "\_"

It is not enough to construct data --- we must compute
with them.  In this section, I describe standard `algebra of
programming' apparatus, but for indexed data structures, and then show
how to implement it for the indexed datatypes described by
\(\D{Desc}\:I\).

Informally, when presenting an inductive datatype as the initial algebra,
|cin : F (MU F) -> MU F|,
for a suitable functor |F : Set -> Set|, we provide the action of
|F| on functions,
lifting operations on elements uniformly to operations on structures
\begin{spec}
mapF : forall {X Y} -> (X -> Y) -> F X -> F Y
\end{spec}
and are rewarded with an \emph{iterator}, everywhere replacing
|cin| by |phi|.
\begin{spec}
foldF : forall {X} -> (F X -> X) -> MU F -> X
foldF phi (cin ds) = phi (mapF (foldF phi) ds)
\end{spec}
We can think of |F| as
a \emph{signature}, describing how to build expressions from
subexpressions, and |MU F| as the syntactic datatype of expressions
so generated. An \emph{algebra} |phi : F X -> X| explains how to
implement each of the signature's expression-forms for values drawn from |X| ---
we say that |phi| is an |F|-\emph{algebra} with carrier |X|. If
we know how to implement the signature, then we can evaluate
expressions: that is exactly what |foldF| does, first using
|mapF| to evaluate the subexpressions, then applying |phi| to
deliver the value of the whole.

Let us play the same game with our operators on |I -> Set|. We must
first characterise the morphisms or `arrows' of |I -> Set| ---
functions which \emph{respect indexing}.
\begin{code}
_-:>_ : forall {I} -> (I -> Set) -> (I -> Set) -> Set
X -:> Y = forall {i} -> X i -> Y i
\end{code}
The usual polymorphic identity and composition specialise readily to these
|-:>| arrows, verifying the standard categorical laws.
We can revert to using unindexed types by instantiating |X| and |Y| with
constant functions, conveniently given by the usual |kc| combinator,
where |kc i S = S|.

%if False
\begin{code}
kc : forall {a b} {A : Set a} {B : Set b} -> A -> B -> A
kc x = \ _ → x
\end{code}
%endif

We are now in a position to equip our descriptions with their functorial
action on arrows.
\begin{code}
map : forall {I X Y} -> (D : Desc I) -> (X -:> Y) -> <! D !> X -:> <! D !> Y
map (say i)       f q         = q
map (sg S D)      f (s , ds)  = s ,    map (D s) f ds
map (ask i ** D)  f (d , ds)  = f d ,  map D f ds
\end{code}

We might correspondingly hope to acquire an iterator, taking any
index-respecting algebra and performing the index-respecting evaluation
of indexed expressions.
\begin{code}
fold : forall {I X}{D : Desc I} -> (<! D !> X -:> X) -> Data D -:> X
fold {D = D} phi << ds >> = phi (map D (fold phi) ds)
\end{code}
Frustratingly, Agda rejects this definition as less than obviously
terminating. Agda's termination oracle cannot see that |map| will apply
|fold phi| recursively only to subterms of |ds|. One might seek to
improve the oracle's perspicacity, or better, to express the requirement
which |map| satisfies by type --- Abel's \emph{sized type}
discipline~\cite{abel:PhD} is certainly adequate to this task.
Locally, however, we can expose a satisfactory subterm structure
just by long-windedly specialising |map| to its instance for |foold|.

\begin{code}
mutual
  foold : forall {I X}{D : Desc I} -> (<! D !> X -:> X) -> Data D -:> X
  foold {D = D} phi << ds >> = phi (mapFold D D phi ds)

  mapFold : forall {I X}(D E : Desc I) -> (<! D !> X -:> X) -> 
            <! E !> (Data D) -:> <! E !> X
  mapFold D (say i)       phi        q  = q
  mapFold D (sg S E)      phi (s , xs)  = s ,             mapFold D (E s) phi xs
  mapFold D (ask i ** E)  phi (x , xs)  = foold  phi x ,  mapFold D E phi xs
\end{code}
We see here the first instance of a recurring pattern in this paper.
We process nodes of recursive structures a little at a time, retaining
a fixed description |D| for the main structure, whilst a helper function
walks through |E|, the description of the current node's tail, invoked
with |E = D|. It reminds me of coding division by primitive
recursion, when I was a boy.

Lots of popular operations can be expressed as folds. For example,
addition\ldots
\begin{code}
addA : Nat -> <! NatD !> (kc Nat) -:> kc Nat
addA y (ze , _)      = y
addA y (su , z , _)  = suc z

_+_ : Nat -> Nat -> Nat
x + y = foold (addA y) x
\end{code}
\ldots and vector concatenation --- note the careful abstraction of \(m\)
in the carrier of the algebra:
\begin{code}
concatA :  forall {X n} -> VecK X n ->
         <! VecDK X !> (\ m -> VecK X (m + n)) -:> (\ m -> VecK X (m + n))
concatA ys (ze , refl)               = ys
concatA ys (su , x , _ , zs , refl)  = x :K: zs

_+K+_ : forall {m n X} -> VecK X m -> VecK X n -> VecK X (m + n)
xs +K+ ys = fold (concatA ys) xs
\end{code}

I hesitate to claim that |fold| delivers the most perspicuous
definitions of these operations, especially given the visual overhead
of the datatype encoding, but the point is that we can exploit the
fact that these operations are |fold|s in reasoning about them, and in
performing further constructions. Epigram, of course, was originally
conceived as a language combining a readable pattern matching syntax
with definition by structural recursion
operators~\cite{conor.james:viewfromleft}, so we may reasonably hope
to have the best of both worlds. Whether or not you view it as
desirable, it is not \emph{necessary} to adopt a pointfree style of
programming to work with recursion schemes.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Ornaments and their Algebras\label{sec:orn}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%format ^-1 = "{}^{\D{ -1}}"
%format _^-1_ = "\_" ^-1 "\_"
%format ok = "\C{ok}"
%format Orn = "\D{Orn}"
%format !~ = "\F{\lfloor}\!"
%format ~! = "\!\F{\rfloor}"
%format !~_~! = !~ "\_" ~!
%format insert = "\C{\Updelta}"
%format ListO = "\F{ListO}"
%format ListD = "\F{ListD}"
%format LIST = "\F{List}"
%format erase = "\F{erase}"
%format ornAlg = "\F{ornAlg}"
%format forget = "\F{forget}"
%format nill = "\F{[]}"
%format :l: = "\F{::}"
%format _:l:_ = "\_" :l: "\_"

In this section, I shall introduce the idea of \emph{ornamenting} an
indexed data structure, combining the business of \emph{decorating} a
datatype with extra stored information and that of \emph{refining} a
datatype with a more subtle index structure. By constructing a fancy
datatype in this way, we establish, for free, an algorithmic relationship
with its plain counterpart.

Suppose we have some description |D : Desc I| of an |I|-indexed family
of datatypes (e.g., lists indexed by |One|).  Now suppose we come up
with a more informative index set |J| (e.g., |Nat|), together with
some function |e : J -> I| which erases this richer information (e.g.,
|!|, the terminal arrow which always returns |<>|). Let us consider
how we might develop a description |D' : Desc J| (e.g., for vectors)
with the same recursive structure as |D|, but richer indexing in an
|e|-respecting way. We should be able to always erase bits of a |Data
D' j| to get an unadorned |Data D (e j)| (e.g., converting vectors
to plain old lists).

How are we to build such a |D'| from |D|? Certainly, wherever
|D| mentions indices |i : I|, |D'| will need an index |j| such that
|e j = i|. It will help to define the \emph{inverse image} of |e|, as
follows:\\
\begin{code}
data _^-1_ {I J : Set}(e : J -> I) : I -> Set where
  ok : (j : J) -> e ^-1 (e j)
\end{code}
That is to say, |ok j : e ^-1 i| if and only if |e j| and
|i| are definitionally equal: only the |j|s in |i|'s inverse
image are |ok|. Notice that when we work with |! : J -> 1|,
 |! ^-1 <>| is a copy of |J|, because |! j| is always |<>| --- if
there is no structure to respect, it is easily respected.

Now, let us think of a language |Orn|, for ornamenting a given
description.  We should be able to mimic the existing structure of
descriptions making sure that every |I|-index is assigned a
corresponding |J|-index. The first three constructors, below, overload
the description constructors and deliver just that capability, but the
fourth, |insert| for `difference', does something more curious ---
it permits us to insert new
non-recursive fields into the datatype upon which subsequent
ornamentation may depend. This will prove important, because we may
need more information in order to decide which |J|-indices to choose
than was present in the original |I|-indexed structure, and we may
want more information, anyway.

\begin{code}
data Orn {I}(J : Set)(e : J -> I) : Desc I -> Set1 where
  say      :  {i : I} -> e ^-1 i ->                                     Orn J e (say i)
  sg       :  (S : Set) -> forall {D} -> ((s : S) -> Orn J e (D s)) ->  Orn J e (sg S D)
  ask_**_  :  {i : I} -> e ^-1 i -> forall {D} -> Orn J e D ->          Orn J e (ask i ** D)
  insert   :  (S : Set) -> forall {D} -> (S -> Orn J e D) ->            Orn J e D
\end{code}

Before we go the length of vectors, let us have a simple but crucial
example, ornamenting natural numbers
to get the type of \emph{lists}. This ornament is a simple decoration
without refinement: a list is a natural number with decorated successors!
\begin{code}
ListO : Set -> Orn One ! NatD
ListO X = sg ZorS (
  ze->                                 say (ok <>)
  su-> insert X \ _ -> ask (ok <>) **  say (ok <>) )
\end{code}
The difference is given by the |insert|, attaching an element of |X|
in the |su| case.

Now, an ornament is no use unless we can extract the new description to
which it leads. To do this, we need only turn |insert| to |sg| and drop
the fancy indices into place.
\begin{code}
!~_~! : forall {I J f}{D : Desc I} -> Orn J f D -> Desc J
!~ say (ok j) ~!       = say j
!~ sg S O ~!           = sg S \ s -> !~ O s ~!
!~ ask (ok j) ** O ~!  = ask j ** !~ O ~!
!~ insert S O ~!       = sg S \ s -> !~ O s ~!
\end{code}
Checking the example, we define
\begin{code}
ListD : Set -> Desc One
ListD X = !~ ListO X ~!
\end{code}
and may then take
\begin{code}
LIST : Set -> Set
LIST X = Data (ListD X) <>

nill : forall {X} -> LIST X
nill = << ze , refl >>

_:l:_ : forall {X} -> X -> LIST X -> LIST X
x :l: xs = << su , x , xs , refl >>
\end{code}
acquiring lists with a `nil' and  `cons'.


\subsection*{Ornamental Algebras}

What use is it to construct lists from numbers in this way? By
presenting lists as an ornament on numbers, we have ensured that
lists carry at least as much information. Correspondingly,
there must be an operation which erases this extra information and
extracts from each list its inner number. In effect, we have made
it intrinsic that lists have \emph{length}.

%if False
\begin{code}
mutual
\end{code}
%endif

More generally, for every ornament |O : Orn J e D|,
we get a forgetful map

\begin{spec}
  forget : forall {I J e}{D : Desc I}(O : Orn J e D) ->
           {j : J} -> Data !~ O ~! j -> Data D (e j)
\end{spec}
which rubs out the |insert| information and restores the less
informative index. As you might expect,
we shall have
\begin{spec}
length : forall {X} -> LIST X -> Nat
length {X} = forget (ListO X)
\end{spec}

With judicious reindexing via composition, we can see |forget| as an
index-respecting function between |J|-indexed sets, and
define it as a |fold|, given a suitable algebra.
\begin{code}
  forget :  forall {I J e}{D : Desc I}(O : Orn J e D) ->
            (Data !~ O ~!) -:> Data D o e
  forget O = foold (ornAlg O)
\end{code}
where |O|'s \emph{ornamental algebra} is given as follows
\begin{code}
  ornAlg :  forall {I J e}{D : Desc I}(O : Orn J e D) ->
            <! !~ O ~! !> (Data D o e) -:> Data D o e
  ornAlg O ds = << erase O ds >>

  erase :  forall {I J e}{D : Desc I}{X : I -> Set} -> (O : Orn J e D) ->
            <! !~ O ~! !> (X o e) -:> <! D !> X o e
  erase (say (ok j))       refl      = refl
  erase (sg S O)           (s , rs)  = s ,  erase (O s) rs
  erase (ask (ok j) ** O)  (r , rs)  = r ,  erase O rs
  erase (insert S O)       (s , rs)  =      erase (O s) rs  -- |s| is erased
\end{code}

The hard work is done by the natural transformation |erase|, good for
plain |I|-indexed stuff in general (so |Data D| in particular),
erasing, as you can see in the last line, just those components
corresponding to a |insert|.
We are also satisfying the index constraints ---
where we have an |(X o e) j| on the left, we deliver an
|X (e j)| on the right, and in the |say| case, the |refl|
pattern unfies the |j|s on the left, ensuring that proof obligation
on the right is simply |e j == e j|. By defining
ornaments relative to descriptions, we ensure a perfect fit.

%if False
\begin{code}
length : forall {X} -> LIST X -> Nat
length {X} = forget (ListO X)
\end{code}
%endif

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Algebraic Ornaments\label{sec:algorn}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%format algOrn = "\F{algOrn}"
%format Le = "\F{Le}"
%format leBase = "\F{leBase}"
%format leStep = "\F{leStep}"
%format safeSub = "\F{safeSub}"

A |<! D !>|-algebra, |phi|, describes a structural method to interpret
the data described by |D|, giving rise to a |fold phi| operation,
applying the method recursively. Unsurprisingly, the resulting tree of
calls to |phi| has the same structure as the original data --- that
is the point, after all. But what if that were, \emph{before} all, the
point?  Suppose we wanted to fix the result of |fold phi| in
advance, representing only those data which would deliver the answer
we wanted.  We should need the data to fit with a tree of |phi|
calls which delivers that answer. Can we restrict our data to exactly
that?  Of course we can, if we \emph{index} by the answer.

For every description |D : Desc I|, every algebra
|phi : <! D !> J -:> J| yields an \emph{algebraic
  ornament}, giving us a type indexed over pairs in |Sg I J| whose first
component must coincide with the original |I|-index --- so the
erasure map is just |fst| --- but whose second component is
computed by |phi|.
My colleagues give a semantic account of algebraic ornaments
in terms of the
\emph{families fibration}~\cite{atkey.ghani.johann:inductiverefinement}.
In order to give a concrete implementation, I compute the algebraic
ornament by recursion on the description |D|, inserting a |J|-value to
index each recursive object asked for
and steadily building a record of arguments for |phi| so that we can
compute and report a |J|-index for the whole node. Here we see another
of this paper's routine techniques, the use of the currying operator,
|cu phi s t = phi (s , t)|, to feed an algebra one mouthful at a time.
\begin{code}
algOrn : forall {I J}(D : Desc I) -> (<! D !> J -:> J) -> Orn (Sg I J) fst D
algOrn          (say i)       phi = say (ok (i , phi refl))
algOrn          (sg S D)      phi = sg S \ s -> algOrn (D s) (cu phi s)
algOrn {J = J}  (ask i ** D)  phi = insert (J i) \ j -> ask (ok (i , j)) ** algOrn D (cu phi j)
\end{code}
Working from left to right along the description, we satisfy
|phi|'s hunger stepwise, until
we are ready to drop the |refl| in at the right end.

Our first example algebra gives us an example algebraic ornament: we can
use the
|addA m| to characterize those numbers of form |m + d|,
acquiring a definition of `less-or-equal', which ornaments the type of
the difference |d|, as follows:
\begin{code}
Le : Nat -> Nat -> Set
Le m n = Data !~ (algOrn NatD (addA m)) ~! (<> , n)

leBase  : forall {m} ->              Le m m
leBase     = << ze , refl >>

leStep  : forall {m n} -> Le m n ->  Le m (suc n)
leStep x   = << su , _ , x , refl >>
\end{code}

As a consequence of this construction, we acquire the
`safe subtraction' function.
\begin{code}
safeSub : (n m : Nat) -> Le m n -> Nat
safeSub n m = forget (algOrn NatD (addA m))
\end{code}
The safety proof does, in fact, encode the difference, so we need merely
decode it.





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Buy Lists, Get Vectors Free}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%format VecO = "\F{VecO}"
%format VecD = "\F{VecD}"
%format VEC = "\F{Vec}"
%format nilv = "\F{[]}"
%format :v: = "\F{::}"
%format _:v:_ = "\_" :v: "\_"
%format toList = "\F{toList}"
%format LengthO = "\F{LengthO}"
%format Length = "\F{Length}"
%format nilL = "\F{nilL}"
%format consL = "\F{consL}"
%format lengthVec = "\F{lengthVec}"
%format makeToVec = "\F{makeToVec}"
%format alloa = "\F{aOoA}"

In section \ref{sec:orn}, we saw how to make type of lists from the
type of natural numbers by an ornament, acquiring an \emph{ornamental
algebra} to measure list length in the process. In section
\ref{sec:algorn}, we learned to extract an \emph{algebraic ornament}
from an algebra, adding an index to a set. Let us put the two together,
taking the algebraic ornament of the ornamental algebra to make new
ornaments from old.

\begin{code}
alloa :   forall {I J}{e : J -> I}{D : Desc I} ->
          (O : Orn J e D) -> Orn (Sg J (Data D o e)) fst !~ O ~!
alloa O = algOrn !~ O ~! (ornAlg O)
\end{code}

Applying this recipe to the list ornament, we acquire the `lists of a
given length', also known as \emph{vectors}.

\begin{code}
VecO : (X : Set) -> Orn (One * Nat) fst (ListD X)
VecO X = alloa (ListO X)

VecD : (X : Set) -> Desc (One * Nat)
VecD X = !~ VecO X ~!

VEC : Set -> Nat -> Set
VEC X n = Data (VecD X) (<> , n)
\end{code}

We can define the vector constructors in terms of our primitive
components.
\begin{code}
nilv   : forall {X} ->                    VEC X zero
nilv = << ze , refl >>

_:v:_  : forall {X n} -> X -> VEC X n ->  VEC X (suc n)
x :v: xs = << su , x , _ , xs , refl >>
\end{code}

Like any other, our new ornament has an ornamental
algebra inducing a forgetful map:
\begin{code}
toList : forall {X n} -> VEC X n -> LIST X
toList {X} = forget (VecO X)
\end{code}

We explained how to define vectors when we explained how to see
lists as a \emph{decoration} of their lengths! This additional
structure becomes manifest once we bring decoration and refinement
together under one roof.


\subsection*{The Same Trick Twice}

We had an ornament, which give us an algebra, which gave us an
ornament, which gave us an algebra. Surely that gives us an ornament
which gives us an algebra! The first time, we got lists indexed by
length; now we get vectors indexed by their lists, otherwise known
as the inductive definition of list length.

\begin{code}
LengthO : (X : Set) -> Orn ((One * Nat) * LIST X) fst (VecD X)
LengthO X = alloa (VecO X)  -- = |alloa (alloa (ListO X))|

Length : {X : Set} -> LIST X -> Nat -> Set
Length {X} xs n = Data !~ LengthO X ~! ((<> , n) , xs)

nilL : forall {X} -> Length {X} nill zero
nilL = << ze , refl >>

consL : forall {X n}{x : X}{xs : LIST X} -> Length xs n -> Length (x :l: xs) (suc n)
consL l = << su , _ , _ , _ , l , refl >>
\end{code}

The forgetful function takes us from the proof of a list's length
to its representation as a vector.

\begin{code}
lengthVec : forall {X n}{xs : LIST X} -> Length xs n -> VEC X n
lengthVec {X} = forget (LengthO X)
\end{code}

We have seen how to build the ornamental hierarchy, and to descend it
with forgetful |fold|s, throwing away index information. To \emph{climb}
the hierarchy, we need |fold|'s dependent cousin, \emph{proof by induction}.
%As it happens, induction can be seen as a fold on an ornament.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%\section{The Initial-Algebraic Ornament Induces Induction}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%%format InitialO = "\F{InitialO}"
%%format Singleton = "\F{Singleton}"
%%format Natty = "\F{Natty}"
%%format zeroey = "\F{zeroey}"
%%format succy = "\F{succy}"
%%format natty = "\F{natty}"
%%format singleton = "\F{singleton}"
%%format singletons = "\F{singletons}"
%%format Everywhere = "\F{Everywhere}"
%%format induction = "\F{induction}"
%%format step = "\F{step}"
%
%Right under our noses, every datatype comes with an algebra
%--- the initial algebra for the functor whose fixpoint gives
%the datatype. Let us consider the algebraic ornament thus
%induced.
%
%\begin{code}
%InitialO : forall {I}(D : Desc I) -> Orn (Sg I (Data D)) fst D
%InitialO D = algOrn D <<_>>
%\end{code}
%
%What this hands us is the \emph{singleton type} construction,
%explaining by inductive definition what it is to be a particular
%element of a datatype.
%
%\begin{code}
%Singleton : forall {I}(D : Desc I){i} -> Data D i -> Set
%Singleton D {i} x = Data !~ InitialO D ~! (i , x)
%\end{code}
%
%For example, we may define what it is to be some number in
%particular.
%
%\begin{code}
%Natty : Nat -> Set
%Natty = Singleton NatD
%
%zeroey : Natty zero
%zeroey = << ze , refl >>
%
%succy : forall {n} -> Natty n -> Natty (suc n)
%succy x = << su , _ , x , refl >>
%\end{code}
%
%It seems that one could easily prove that every |Nat| is |Natty|:
%\begin{code}
%natty : (n : Nat) -> Natty n
%natty << ze , refl >>      = zeroey
%natty << su , n , refl >>  = succy (natty n)
%\end{code}
%
%Of course, there is nothing special about |Nat| in this construction.
%Let us make it entirely generic.
%
%\begin{code}
%mutual
%
%  singleton : forall {I}(D : Desc I){i}(d : Data D i) -> Singleton D d
%  singleton {I} D << ds >> = << singletons D <<_>> ds >> where
%
%    singletons : forall (D' : Desc I)(c : <! D' !> (Data D) -:> Data D) ->
%      {i : I}  (ds : <! D' !> (Data D) i) ->
%               <! !~ algOrn D' c ~! !> (Data !~ InitialO D ~!) (i , c ds)
%    singletons (say i)        c refl      = refl
%    singletons (sg S D')      c (s , ds)  = s ,                  singletons (D' s) (c o _,_ s) ds
%    singletons (ask i ** D')  c (d , ds)  = d , singleton D d ,  singletons D' (c o _,_ d) ds
%
%\end{code}
%
%The |singleton| construction relies on a particular use of induction,
%implemented here as a structurally recursive program with a dependent
%type.
%
%
%\subsection{Induction as a Singleton Fold}
%
%All other induction reduces to the singleton construction by
%iteration. To see how, firstly consider the `predicate transformer':
%
%\begin{code}
%Everywhere : forall {I}{D : Desc I} -> (Sg I (Data D) -> Set) -> Sg I (<! D !> (Data D))  -> Set
%Everywhere {I}{D} P (i , ds) = <! !~ InitialO D ~! !> P (i , << ds >>)
%\end{code}
%
%If |P| is a set indexed by (|I| and) |Data D|, then |Everywhere P ds|
%collects a |P| for each |d| in |ds|. It is the type of the inductive
%hypothesis one needs when proving |P (i , << ds >>)|.
%
%We may thus state and prove a generic induction principle:
%
%\begin{code}
%induction :  forall {I}(D : Desc I)(P : Sg I (Data D) -> Set) ->
%             (forall {i}(ds : <! D !> (Data D) i) -> Everywhere P (i , ds) -> P (i , << ds >>)) ->
%             forall {i}(d : Data D i) -> P (i , d )
%induction {I} D P p d = fold !~ InitialO D ~! step (singleton D d) where
%  step : <! !~ InitialO D ~! !> P -:> P
%  step {i , << ds >>} hs = p ds hs
%\end{code}
%
%
%
%With modest repackaging, the inductive step function becomes an
%algebra, not for |<! D !>|, but for its initial-algebraic ornament,
%|<! !~ InitialO D ~! !>|, and induction becomes a fold. Please note
%that the |singleton| construction is \emph{not} a fold: induction has
%not been eliminated, only contained in one Promethean act of theft
%from our dependent host language. Similarly, the |step| function involves a
%dependent case analysis on the index pair, so again we have pushed the
%dependency into one corner: we need Lambek's lemma in some form, to
%know that pattern matching really inverts construction with |<<_>>|.
%
%
%\subsection{Indexing with an Algebra}
%
%Consider an algebra, |length|'s algebra (|ornAlg (ListO X)|) for example,
%|phi : <! D !> J -:> J| in general. We can make the |phi|-indexed |D|s
%by algebraic ornament,
%\begin{code}
%Indexed : forall {I J}(D : Desc I)(phi : <! D !> J -:> J) -> Sg I J -> Set
%Indexed D phi = Data !~ algOrn D phi ~!
%\end{code}
%
%Let us make sure that we can `remember' the index of some plain data,
%using the |fold| to compute it.
%
%\begin{code}
%
%pr : forall {I}{J K : I -> Set} -> (J -:> K) -> Sg I J -> Sg I K
%pr f ij = (fst ij , f (snd ij))
%
%ammo : forall {I}{J K : I -> Set}(D : Desc I)(phi : <! D !> J -:> J)(psi : <! D !> K -:> K)(f : J -:> K)
%       (q : forall {i} -> (js : <! D !> J i) ->  psi (map D f js) == f (phi js)) ->
%       {X : Sg I J -> Set}{Y : Sg I K -> Set}(h : X -:> (Y o pr f)) ->
%       <! !~ algOrn D phi ~! !> X -:> <! !~ algOrn D psi ~! !> Y o pr f
%ammo (say i) phi psi f q h refl = cong (_,_ i) (q refl)
%ammo (sg S D) phi psi f q h (s , xs) = s , ammo (D s) (phi o _,_ s) (psi o _,_ s) f (q o _,_ s) h xs
%ammo (ask i ** D) phi psi f q h (j , x , xs) =
%   f j , h x , ammo D (phi o _,_ j) (psi o _,_ (f j)) f (q o _,_ j) h xs
%
%
%remember : forall {I J}(D : Desc I)(phi : <! D !> J -:> J) -> {i : I}(d : Data D i) -> Indexed D phi (i , fold D phi d)
%remember D phi = induction D (un \ i d ->  Indexed D phi (i , fold D phi d))
%  (\ ds hs -> << ammo D <<_>> phi (fold D phi) (\ _ -> refl) id hs >>)
%\end{code}
%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Induction}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%format All = "\F{All}"
%format induction = "\F{induction}"
%format everywhere = "\F{everywhere}"
%format everywhereInduction = "\F{everyInd}"
%format assoc = "\F{assoc}"

We may prove a generic induction principle for all our datatypes at
once. The construction amounts to an effective treatment of the
fibrational analysis due to Bart Jacobs and
Claudio Hermida~\shortcite{DBLP:journals/iandc/HermidaJ98},
recently generalised by my colleagues, Neil Ghani, Patricia Johann and
Cl\'{e}ment Fumex~\shortcite{neil.patty.clem:induction}.
Let me make the statement.

\begin{spec}
  induction :  {I : Set}(D : Desc I)
               (P : {i : I} -> Data D i -> Set) ->
               ({i : I}(ds : <! D !> (Data D) i) -> All D P ds -> P << ds >>) ->
               {i : I}(x : Data D i) -> P x
\end{spec}

Unpacking this statement, what do we have? For the |I|-indexed
datatype with description |D|, let |P| be a `predicate'---I have
slipped into the language of propositions and proof, but the same
construction works for programming, too. To show that |P| holds for
all |x|, we must show that |P| holds for each parent |<< d >>|, given
that it holds for all the |D|-children in |d|. We can compute what it
means for |P| to hold for all those children, building a tuple of
|P|s.

\begin{code}
All :  {I : Set}(E : Desc I){D : I -> Set}
       (P : {i : I} -> D i -> Set)
       {i : I} -> <! E !> D i -> Set
All (say i)       P x        = One 
All (sg S E)      P (s , e)  = All (E s) P e
All (ask i ** E)  P (d , e)  = P d * All E P e
\end{code}

My colleagues rightly point out that |All| is, up to bureaucratic
isomorphism, the functor on indexed sets given by the \emph{initial}
algebraic ornament, describable as |!~ algorn D <<_>> ~!|. Ornamenting
a datatype by its initial algebra expresses exactly the
\emph{singleton} property of being \emph{constructed uniquely from
constructors}, which holds for all elements, of course. The essence of
the fibrational analysis is that induction on a datatype amounts to
iteration on its family of singletons. I chose not to use that
construction in this paper only because my simple but rigid |Desc|
formulation renders it awkwardly, where the |All| above neatly
computes the tuple structure from the record which indexes it.

The implementation of |induction| is thus suspiciously like that of
|fold|. As a first attempt, we may try to define |induction| via a
|map|-like operator.

\begin{spec}
induction D P p << ds >> = p ds (everywhere D P (induction D P p) ds)
\end{spec}
\begin{code}
everywhere :  {I : Set}(E : Desc I){D : I -> Set}
              (P : {i : I} -> D i -> Set) ->
              ({i : I}(x : D i) -> P x) ->
              {i : I}(d : <! E !> D i) -> All E P d
everywhere (say i)       P p _        = <>
everywhere (sg S E)      P p (s , e)  = everywhere (E s) P p e
everywhere (ask i ** E)  P p (d , e)  = p d , everywhere E P p e
\end{code}

As with |fold|, Agda cannot see why the unapplied recursive |induction|
is justified: it does not trust that |everywhere| will apply the given
method only to subobjects of |d|. Again, we can make the structural
recursion clear by specializing |everywhere| to |induction|.

\begin{code}
mutual
  induction : {I : Set}(D : Desc I)(P : {i : I} -> Data D i -> Set) ->
              ({i : I}(ds : <! D !> (Data D) i) -> All D P ds -> P << ds >>) ->
              {i : I}(x : Data D i) -> P x
  induction D P p << ds >> = p ds (everywhereInduction D D P p ds)
  everywhereInduction :
    {I : Set}(E D : Desc I)
    (P : {i : I} -> Data D i -> Set) ->
    ({i : I}(d : <! D !> (Data D) i) -> All D P d -> P << d >>) ->
    {i : I}(d : <! E !> (Data D) i) -> All E P d
  everywhereInduction (say i)       D P p _        = <>
  everywhereInduction (sg S E)      D P p (s , e)  = everywhereInduction (E s) D P p e
  everywhereInduction (ask i ** E)  D P p (d , e)  = induction D P p d , everywhereInduction E D P p e
\end{code}

We can use |induction| to prove properties of specific functions at a
specific type. Here, for example, is what Bundy calls `the E. Coli of
inductive proof', associativity of addition:

\begin{code}
assoc : (x y z : Nat) -> ((x + y) + z) == (x + (y + z))
assoc x y z = induction NatD (\ x -> ((x + y) + z) == (x + (y + z)))
  (un (  ze-> (\ _ _ -> refl)
         su-> un (\ x _ -> un \ H _ -> suc // H)
  )) x
\end{code}

Agda does not support a pattern matching presentation of programming
or tactical proof with hand-crafted induction schemes, so I am obliged
to write an inscrutable proof expression, making use of the uncurrying
operator |un f (s , t) = f s t| to split tuples. Moreover, while
programmers rejoice when intermediate type information is
suppressable, those very types are the intermediate hypotheses and
subgoals which show the pattern of reasoning in \emph{proofs}. The
Curry-Howard correspondence does not extend to a good discipline of
documentation! What you can perhaps make out from my proof is that
|assoc| is not itself a recursive definition: rather, the inductive
step unpacks the inductive hypothesis, |H|, and delivers |suc // H|,
the proof that applying |suc| to both sides preserves the equation.


\subsection*{Remembering, wholesale}

%format remember = "\F{remember}"
%format meld = "\F{meld}"
%format Dphi = "\F{D\!^{\phi}}"
%format psi = "\V{\psi}"
%format toVec = "\F{toVec}"

We can also use |induction| in generic programming. With apologies to
Philip K. Dick, I shall show how to implement the inverse of |forget|,
for every \emph{algebraic} ornament.

\begin{code}
remember :  forall {I J}{D : Desc I}(phi : <! D !> J -:> J) -> let Dphi = !~ algOrn D phi ~! in
            {i : I} -> (d : Data D i) -> Data Dphi (i , foold phi d)
\end{code}

The type of |remember| says that we can turn a plain old |d| into its
fancier |J|-indexed counterpart, delivering the very index computed by
|foold phi d|. For example, a list becomes a vector of its own |length|.

The implementation of |remember| is framed by an |induction|, but the
main work consists of |meld|ing the non-recursive data from the plain
record with the fancy recursive data from the inductive hypotheses,
inserting indices computed by |foold phi| where required.

\begin{code}
remember {I}{J}{D} phi =
  induction D (\ {i} d ->  Data Dphi (i , foold phi d)) (\ ds hs -> << meld D phi ds hs >>) where
           Dphi = !~ algOrn D phi ~!
           meld :  (E : Desc I)(psi : <! E !> J -:> J){i : I}(e : <! E !> (Data D) i) ->
                   All E (\ {i} d -> Data Dphi (i , foold phi d)) e ->
                   <! !~ algOrn E psi ~! !> (Data Dphi) (i , psi (mapFold D E phi e))
           meld (say i)       psi refl     hs        = refl
           meld (sg S E)      psi (s , e)  hs        = s , meld (E s) (cu psi s) e hs
           meld (ask i ** E)  psi (d , e)  (h , hs)  = j , h , meld E (cu psi j) e hs where j = foold phi d
\end{code}

Again, |meld| requires a recursion over the datatype structure, with
|E| carrying the remainder of the description (initially |D|) and
|psi| its remaining algebra (initially |phi|). As in |algOrn| itself,
|psi| is repeatedly curried and fed one piece at a time.

Let us check our example.

\begin{code}
toVec : {X : Set}(xs : LIST X) -> VEC X (length xs)
toVec {X} = remember (ornAlg (ListO X))
\end{code}

To show that |remember phi| and |forget (algOrn phi)| are mutually
inverse again requires |induction|. This is left as an exercise for
the reader.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The Recomputation Lemma}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%format Recomputation = "\F{Recomputation}"
%format Ophi = "\F{O\!^{\phi}}"
%format fuse = "\F{fuse}"
%format rewrite = "\mathkw{rewrite}"
%format Epsi = "\F{E\!^{\psi}}"


Suppose we have a vector |xs| whose length index is |n|: what is
|length (toList xs)|? We should be astonished if it were anything other
than |n|, but how can we be sure? In this section, I shall prove that
an index given by an algebraic ornament can be recomputed by the
corresponding |foold|.

Let us state this property formally. Given a description |D| and a |<!
D !>|-algebra |phi| over some |J|, we may construct the algebraic
ornament |Ophi|, and thence the fancy type |Dphi|. |Dphi| is indexed
by pairs, with the second component being a |J|. We may state that
every fancy |x|'s |J|-index can be recovered from its plain
counterpart by |foold phi|.

\begin{code}
Recomputation :  forall {I J}(D : Desc I)(phi : <! D !> J -:> J) -> 
                 let Ophi = algOrn D phi ; Dphi = !~ Ophi ~! in
                 {ij : Sg I J}(x : Data Dphi ij) -> foold phi (forget Ophi x) == snd ij
\end{code}

The proof goes by |induction| on the fancy type, with an inner lemma
fusing |foold phi| with |forget Ophi|.

\begin{code}
Recomputation {I}{J} D phi =
  induction Dphi (\ {ij} x ->  foold phi (forget Ophi x) == snd ij) (fuse D phi) where
    Ophi = algOrn D phi ; Dphi = !~ Ophi ~!
\end{code}

Of course, the |forget| is really a |foold (ornAlg Ophi)|, so the heart 
of the proof shows how the two |mapFold|s combine to feed the algebra
what we expect. The type of |fuse| follows our trusty pattern, abstracting
the unprocessed description |E| and its hungry algebra |psi|.

\begin{code}
    fuse :  (E : Desc I)(psi : <! E !> J -:> J) -> let Epsi =  !~ algOrn E psi ~! in
            {ij : Sg I J}(e : <! Epsi !> (Data Dphi) ij) ->
            All Epsi (\ {ij} x -> foold phi (forget Ophi x) == snd ij) e ->
            psi (mapFold D E phi (erase (algOrn E psi) (mapFold Dphi Epsi (ornAlg Ophi) e)))
              == snd ij
    fuse (say i)       psi  refl         hs                      = refl
    fuse (sg S E)      psi  (s , e)      hs                      = fuse (E s) (cu psi s) e hs
    fuse (ask i ** E)  psi  (j , x , e)  (h , hs)     rewrite h  = fuse E (cu psi j) e hs
\end{code}

In the |ask i ** E| case, |j| is the index of |x|, and the
goal asks us to show that
\[
  |psi (foold phi (forget Ophi x) , | \ldots |) == snd ij|
\]
Agda allows us to |rewrite| by inductive hypothesis,
\[
|h : foold phi (forget Ophi x) == j|
\]
so that we can feed |j| to |psi| and continue. When we reach the end
of the record, we learn the value of its index |ij|---exactly the value we need.

The recomputation lemma is, in some sense, a statement of the
obvious. It tells us that if we can perform a construction at a higher
level of precision, we automatically know something about its less
precise counterpart.


\subsection*{A Weapon of Math Construction}

%format myf = "\F{f}"
%format myg = "\F{g}"
%format myf' = "\F{f}^{" phi "}"

Standing the recomputation lemma on its head, we acquire a construction
method. Suppose we want to write some function
\[
  |myf : A -> Data D i|
\]
whose specification is of form |foold phi o myf == myg|. That is,
the output must have a particular interpretation, according to some
algebra |phi|. Algebraically ornamenting
|D| by |phi| allows us to bake the specification into the type of
the program. We can try to implement a fancier function:
\[
  |myf' : (a : A) -> Data <! !~ algOrn D phi ~! !> (i , myg a)|
\]
If we succeed, we may define
\[
  |myf = forget (algOrn D phi) o myf'|
\]
and deduce that the specification is satisfied, gratis. Recomputation
gives us that
\[
|foold phi (myf a) == foold phi (forget (algOrn D phi) (myf' a)) == myg a |
\]

The outside world need not know that we used a rather fancy type to
construct |myf| correctly. The ornamentation technology allows us to
localize the use of the high precision type. Let us put this method
to work.


\section{Compiling Hutton's Razor Correctly}

%format Exp = "\D{Exp}"
%format val = "\C{val}"
%format plus = "\C{plus}"
%format eval = "\F{eval}"
%format Code = "\D{Code}"
%format CODE = "\F{Code}"
%format CodeD = "\F{CodeD}"
%format Op = "\D{Op}"
%format PUSH = "\C{PUSH}"
%format ADD = "\C{ADD}"
%format SEQ = "\C{SEQ}"
%format opCodeD = "\F{opCodeD}"
%format xi = "\F{\upxi}"
%format Sem = "\F{Sem}"
%format exec = "\F{exec}"
%format compile = "\F{compile}"
%format compile' = "\F{compile}^{" xi "}"
%format compileCorrect = "\F{compileCorrect}"

James McKinna suggested that I investigate the following example,
inspired by Graham Hutton's \emph{modus operandi}. Consider a minimal
language of expressions---natural numbers with addition, sometimes
referred to as ``Hutton's Razor''. By way of a reference semantics, we
may readily define an interpreter for this language, summing all the
numerical leaves in a tree of additions.  However, we might prefer to
compile such expressions, perhaps to a simple stack machine. A correct
compiler will guarantee to produce code which respects the reference
semantics. We shall extract this result \emph{for free} from the
recomputation lemma.

Our expression language certainly has a description in |Desc One|, but
let us define it directly: we shall not need to tinker with the
structure of expressions, so we may as well see what we are doing.

\begin{code}
data Exp : Set where
  val   : ANat -> Exp
  plus  : Exp -> Exp -> Exp
\end{code}

The reference semantics is given by a straightforward recursion, which
could certainly be given as a |foold|.

\begin{code}
eval : Exp -> ANat
eval (val n)     = n
eval (plus a b)  = eval a +A eval b
\end{code}

Let me direct our primary attention, however, to the stack machine
code. For convenience, I define it as a tree structure with sequential
composition as a constructor: one may readily flatten the tree at a
later stage.  For saftey, I index code by the initial and final
\emph{stack height} at which it operates. Given directly, we might
declare code thus:

\begin{code}
data Code : (ANat * ANat) -> Set where
  PUSH  : forall {i} ->      ANat ->                          Code (i , sucA i)
  ADD   : forall {i} ->                                       Code (sucA (sucA i) , sucA i)
  SEQ   : forall {i j k} ->  Code (i , j) -> Code (j , k) ->  Code (i , k)
\end{code}

Note how the indexing ensures that the stack cannot underflow: |ADD|
may only be coded when we are sure that the stack holds at least two
values and it decrements the stack height; |PUSH| increments stack height;
|SEQ| ensures that code fragments fit together, domino-style.
One could, of course, consider |Code| to be a stack-safe ornament on
unsafe code, itself an ornament on plain binary trees, but the point of
this example is to push in the other direction, and add yet more
indexing.
Accordingly, let us translate this declaration systematically to a
description. I declare an enumeration for the constructors, then
define the description by case analysis.

\begin{code}
data Op : Set where PUSH ADD SEQ : Op

CodeD : Desc (ANat * ANat)
CodeD = sg Op opCodeD where
  opCodeD : Op ->  Desc (ANat * ANat)
  opCodeD PUSH   =  sg ANat \ i -> sg ANat \ _ ->    say (i , sucA i)
  opCodeD ADD    =  sg ANat \ i ->                   say (sucA (sucA i) , sucA i)
  opCodeD SEQ    =  sg ANat \ i -> sg ANat \ j -> sg ANat \ k ->
                      ask (i , j) ** ask (j , k) **  say (i , k)

CODE : (ANat * ANat) -> Set
CODE = Data CodeD
\end{code}

Now, the semantic object associated with a given code fragment is the
function it induces, mapping an initial stack to a final stack, where
stacks are just numeric vectors of the required height.

\begin{spec}
Sem : (ANat * ANat) -> Set
Sem (i , j) = Vec ANat i -> Vec ANat j
\end{spec}

%if False
\begin{code}
Sem : (ANat * ANat) -> Set
Sem ij = Vec ANat (fst ij) -> Vec ANat (snd ij)
\end{code}
%endif

We can then give the code its semantics by defining the
`execution algebra' for its syntax.

\begin{spec}
xi : <! CodeD !> Sem -:> Sem
\end{spec}

If we expand the definitions in that type, Agda allows us the
following implementation.

\begin{code}
xi : forall {ij} -> <! CodeD !> Sem ij -> Vec ANat (fst ij) -> Vec ANat (snd ij)
xi (PUSH , _ , n , refl)             ns               = n :: ns
xi (ADD , _ , refl)                  (n :: m :: ns)   = (m +A n) :: ns
xi (SEQ , _ , _ , _ , f , g , refl)  ns               = g (f ns)

exec : CODE -:> Sem
exec = foold xi
\end{code}

We can now state our objective formally, namely to define
\begin{spec}
compile : forall {i} -> Exp -> CODE (i , sucA i)
\end{spec}
such that
\[
|exec (compile e) ns == eval e :: ns|
\]
but as |exec| is |foold xi|, let us deploy the above method, and try to
define a fancier, manifestly correct version:

\begin{code}
compile' : forall {i}(e : Exp) -> Data !~ algOrn CodeD xi ~! ((i , sucA i) , _::_ (eval e))
\end{code}

The ornamented code type is indexed by the code's behaviour, as well
as by stack height information. We shall only succeed in our efforts
if we can deliver code which pushes the given expression's value.
Here goes nothing!

\begin{code}
compile' (val _)     =  << PUSH , _ , _ , refl >>
compile' (plus a b)  =  << SEQ , _ , _ , _ , _ , compile' a , _ , << SEQ , _ , _ , _ , _ , compile' b , _ , 
                            << ADD , _ , refl >>
                        , refl >> , refl >>
\end{code}

As you can see, Agda has been able to infer all of the indexing
details.  The basic plan---push values, compile summands then
add---was all we had to make explicit. Indeed, we were able to
suppress even the number pushed in the |val| case, as no other value
satisfies the specification! We may now define |compile| and prove it
correct at a stroke!

\begin{code}
compile : forall {i} -> Exp -> CODE (i , sucA i)
compile = forget (algOrn CodeD xi) o compile'

compileCorrect :  forall (e : Exp){i} -> exec (compile {i} e) == _::_ (eval e)
compileCorrect e = Recomputation CodeD xi (compile' e)
\end{code}

To be sure, this construction took some care and benefited from the
simplicity of the language involved. For one thing, it was crucial to
compile the summands in left-to-right order: had we reversed the order,
we should have needed the commutativity of |+A| to persuade the
type checker to accept |compile'|. More seriously, we escaped some
difficulty because our language has only expressions, not control:
had we included, say, conditional expressions, we should have
been obliged to prove that the actual behaviour, choosing which branch
to execute, is equivalent to the reference behaviour, executing both
branches and choosing between their values. These proofs are easy,
but they are not \emph{nothing}.

What, then, is the essence of this method? Rather than programming by
iteration then proving correctness by the corresponding induction, we
do both in tandem. Those steps of the proof which amount to rewriting
by the inductive hypotheses vanish. For our example, that happens to
be the whole of the proof. In general, we should expect some
obligations to survive. Effectively, the construction internalizes
aspects of the basic proof strategy delivered in Coq by the `Program'
tactics of Catherine Parent and Matthieu Sozeau~\cite{parent:program,sozeau:thesis}: these start from a recursive program and
initiate a proof of its correctness by the corresponding induction,
leaving the remaining proof obligations for the user.


\section{Discussion}

In this paper, I have exploited a \emph{universe} construction to give
a coding system not only for individual datatypes, but for annotation
and refinement relationships \emph{between} datatypes. By making these
connections explicit and first class, I was able to give generic
implementations of some standard components typically churned out by
hand. From the ornament expressing that lists are `natural numbers
with annotations on successor', I acquired the |length| function as
the |foold| of the ornamental algebra, then the notion of vector as an
algebraic ornament, together with operations to shunt data up the
ornamental hierarchy. I showed how to acquire cheap proofs for low
level programs by using ornaments locally to work at a higher level of
precision in the first place. My experiments take the form of Agda
programs, typed, total, and available online.

I hasten to add that I do not claim ornaments provide a viable,
scalable methodology for Agda programming, or that the rudimentary
universe I use in this paper is optimal in practice. Rather, I am
grateful that Agda provides a convenient platform for experimenting
with the basic idea and delivering proof of concept. Before we can
really get to work with this technology, however, we must ensure that
our programming languages are geared to support it. Agda delivers a
pleasant programming experience for its native |data|-declared types:
it is far from pleasant to construct and manipulate their encoded
counterparts in our universe, but not for any deep reason. Good
language support for encoded data has not, thus far, been a priority,
but it is surely possible to repurpose the existing |data| declaration
as mere sugar for the \emph{definition} of the corresponding code, and
to ensure that those codes carry enough information (e.g., about
constructor names, implicit argument conventions, and so forth) to
sustain the readability to which we are accustomed.

Libraries should deliver encoded datatypes, to be taken as themes for
local variation, ensuring that programmers can work with the precision
appropriate to the task at hand without compromising the broader
exchange of data. We should not lose the general functionality of a
list library just because it is sometimes convenient to work with the
precision of vectors, or ordered lists, or ordered vectors, or any of
the other multifarious possibilities which we are now free to farm. At
the same time, we might develop libraries of ornaments. Nobody should
have to think about how to index a particular data structure by its
number of nodes, or a bound on its depth, or its flattening to a
sequence: such recipes belong in the repertoire. Declaring---rather
than defining---datatypes should now be seen as an impediment to the
properly compositional data design process, punished by payment for
what is rightfully free. As the Epigram team has shown, it is not even
necessary to declare the datatype which is used for the descriptions
of datatypes: with care, and a handful of predefined components, a
sufficiently expressive universe can be persuaded to appear as if it
is self-encoded~\cite{chapman.dagand.mcbride.morris:levitation}.

We are ready to begin an ornamental reimagining of programming. Once
aware of the annotation relationship between numbers and lists, for
example, we can ask just what extra is needed to develop concatenation
from addition. Intuitively, we should just require a function to
compute the decoration for the output successor from the decoration on
the input successor: if we work polymorphically, parametricity tells
us there is \emph{no choice} for the output but to copy the input. By
starting not from thin air and inspiration, but rather from a tangible
template, we should not only save perspiration, but also achieve
greater perspicuity. The proof that the length of a concatenation is
the sum of the lengths of its pieces currently requires us to observe
a coincidence, when it should rather be the direct consequence of
an ornamental construction.

There is much to do, both in theory and in practice. On the theory
side, we should seek a more abstract characterization of ornaments,
independent of the particular encoding of datatypes at work. The
theory of \emph{containers} and \emph{indexed containers} seem apt to
the task and an exploration is in
progress~\cite{alti:cont-tcs,alti.morris:ix}. We should also consider
alternative formulations of ornamentation, perhaps as a relation
between two descriptions yielding a forgetful map from one to the
other. Where in this paper, I consider only \emph{insertion} of new
information, we might also want to \emph{delete} old information,
provided we give a way to recover it in the forgetful map. Combining
insertion with deletion, we would acquire the general facility to
rearrange data structures provided the overall effect is to upgrade
with more information. The idea of extending a datatype, stood on its
head, is an ornament of this character---restricting constructor
choice generates a more specific type which obviously embeds in the
original. A formal understanding of the corresponding modifications to
programs might have a profound impact on engineering practice,
reducing the cost of change.

In practical terms, a key question is just how this technology should
be delivered to the programmer. How do I give a datatype, not as a
standalone declaration, but as an ornament? How do I collect my free
programs and theorems? At the moment, our usual means to refer to
particular components of index information tends to be rather
\emph{positional} and is thus unlikely to scale: can we adapt
\emph{record} types to fit this purpose? Can we minimize the cost of
changing representations? It should be possible to store an ornamented
data structure as the dependent pair of the plain data with its
ornamental extras, manipulating the two in sync, and ensuring that the
forgetful function is a constant-time projection in practice. For
algebraic ornaments, the additional information is effectively
propositional---the evidence for the recomputation lemma---and should
thus require no run-time space.

Meanwhile, there are plenty of ornaments which are not algebraic: what
other ornament patterns can we identify and systematize? Where
algebraic ornaments bubble descriptive indices up from the leaves,
there must surely be ornaments which push presciptive indices down
from the root or thread before-and-after indices in a static traversal
of the data. We can write first-class programs with attribute
grammars~\cite{attributes} --- let us also apply a similarly
compositional analysis to first-class \emph{types}.

Dependent types are attractively principled, but they will catch on
in practice only when they enable the programmers
who use them to outperform the programmers who do not. In certain
specialised fields where precision is at a particular premium it can
be profitable to bash away with today's technology, armed to the
teeth with the latest tactics. But where productivity is the key, it
is the programs we need not write ourselves which determine the
effectiveness of a technology. The key to constructing programs is
the organisation of data, and that is at last in our hands.



\bibliographystyle{jfp}
\bibliography{Ornament}



\end{document}
