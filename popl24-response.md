We would like to thank the authors for their thorough reviews. 

# Revew A 
# Revew B
# Revew C 
# Revew D

This review highlights four major areas of concern: 

1. The novelty of the contribution

This concern observes that the pattern unification algorithm is not
especially novel, and asks if the ideas in our categorical semantics
also exist in the literature.

We agree that the core steps of our algorithm are essentially the same
as in other papers: pattern unification algorithm is pattern
unification, regardless of the details of how it is presented.

However, our semantics for metavariables does differ in a critical way
from prior semantics of metavariables (such as that of Hsu et al, as
well as those Fiore's and Hamana's). Those models permit interpreting
*general* metavariables -- i.e., a metavariable can be instantiated
with a full substitution of arbitrary terms. A consequence of this is
that they contain the semantic analogues of problems outside the
pattern fragment, such as `M x x ?= N x x`. Since problems like this
do not have most general unifiers, the more general categories in the
literature correspondingly do not always have suitable equalisers. 

However, the pattern fragment is much more restrictive: a metavariable
can only be instantiated with a disjoint collection of free variables,
ensuring that mgu's can be found (if they exist). Our semantics has
been engineered so that it can *only* interpret metavariable
instantiations in the pattern fragment, and cannot interpret full
metavariable instantiations. [TODO: does one of the reviewers mention
this?]

This restriction gives our model much stronger properties, enabling us
to characterise each part of the pattern unification algorithm in
terms of universal properties. This lets us extend Rydeheard and
Burstall's proof to the pattern case. No prior semantics can be used
for this purpose. 

2. Are arities just vectors of variables without type information?
   How can this possibly extend to dependent types?

This concern is whether our notion of arity is too limited, as a
vector of variables without type information.

Our notion of arity is **not** limited to a vector of variables
without type information. As reviewer A notes, in section 7 we give
examples which show that our notion of arity includes the sorts of the
inputs and the output of the result. As a result, we are performing
unification on intrinsically well-sorted terms, and our correctness
theorem ensures that the result of unification is always a well-typed 
subsitution whose application results in well-typed terms. 

For example, the instance of our unification algorithn for System 
F will never confuse type and term variables, nor will it produce
ill-typed terms or substitutions. Likewise, the example of ordered
unification will never produce substitutions which require exchange
or any other structural rule. 

As we say in the paper, extending our approach to fully
dependently-sorted theories is future work. However, the fact that our
approach works for System F (which permits a light dependency on
types) makes us hopeful.

3. Can our approach handle equations such as beta/eta-laws?

Finally, the last question in this concern asks whether our algorithm
supports unification modulo equational laws like the β- and η-laws of
the lambda calculus. 

Our algorithm is generic over a notion of signature, and so does not
"know" anything about the lambda calculus. Since our definition of
GB-signatures does not carry an equational theory with it, the core
algorithm works only on terms modulo α-equivalence, and works the same
regardless of the signature, whether λ-calculus, π-calculus, or
anything else.

However, in the specific case of the lambda calculus, every typed
lambda term has a normal form, and furthermore, the syntax of the
normal forms can be specified by a GB-signature. As a result, we can
do unification modulo βη by pre-normalising the terms and doing
unification on normal forms, along the lines of Vezzosi and
Abel[1]. (This is also similar to the approach of Abel and Pientka.)
In the final version of the paper, we will give this as an extended
example.

[1] A Categorical Perspective on Pattern Unification, Vezzosi-Abel, RISC-Linz 2014

4. Motivation -- is LF-style unification already enough?

This concern asks if pattern unification for LF-style type theories
can already be used to emulate our results with a suitable choice of
LF signature. The answer to this question is no, it cannot. In fact,
LF signatures and GB-signatures are strictly incomparable in power.

LF-style signatures already handle type dependency (which is future
work for us), but there are also GB-signatures which cannot be encoded
with an LF signature. For example, GB-signatures allow us to express
pattern unification for ordered lambda terms. This is (to our
knowledge) completely novel -- even Schack-Nielsen and Schürman's
pattern unification algorithm for linear types assumes the
admissibility of exchange.







POPL 2024 Paper #265 Reviews and Comments
===========================================================================
Paper #265 Generic pattern unification


Review #265A
===========================================================================

Overall merit
-------------
B. Weak accept: I lean towards acceptance.

Reviewer expertise
------------------
Y. Knowledgeable: I am knowledgeable about the topic of the paper (or at
   least key aspects of it).

Summary of the paper
--------------------
The authors present an Agda implementation of pattern unification, parameterized over a novel notion of generalized binding signature whose instances include the untyped, simply-typed, and ordered lambda calculi, and System F. They provide paper proofs that their algorithm is sound, complete, and terminating, based on a categorical semantics of most general unifiers as equalizers, generalizing earlier work of Barr and Wells and Rydeheard and Burstall, among others, on first-order unification.

Assessment of the paper
-----------------------
Pattern unification is an essential ingredient of many type inference algorithms, so I am convinced by the paper's goal of trying to formulate the problem statement and algorithm in a clean, abstract, and general way, and I think that the paper does a reasonable job of fulfilling those goals. In particular I want to praise the use of dependent types as a way to enforce some but not all of the necessary invariants -- mechanization is not all-or-nothing.

My reservation -- besides some presentational complaints that could easily be fixed in a revision -- is that I am (genuinely!) not sure how novel the ideas are. For example, the categorical semantics struck me as such a direct generalization of the ideas of Rydeheard and Burstall that I was shocked when I could not find a categorical description of pattern unification along these lines in the literature.

Indeed I am not very familiar with the literature on unification (although am moderately familiar with the topic), and in reviewing this paper I was surprised at how difficult it was to compare older papers, each of which concerns a slightly different scenario. Perhaps this indicates that the POPL community is in desperate need of a paper like this one. I don't know. My assessment of B indicates "accept, but with low confidence."

The notion of pattern-friendly generalized binding signature is likely the most novel of the paper's contributions, but I would have liked to see a more in-depth comparison to the many other notions of abstract binding signature that have been developed over the years, several of which are cited. Why couldn't you adapt one of those?

Detailed comments for authors
-----------------------------
The layout and pagination of figures in Section 2 is so bad that it really impeded my ability to read the paper. The figures do not appear in the order that they are explained, and the explanations appear many pages away from the figures themselves. _Please, please fix this._ For example:
- The explanation of Figure 3 (on page 5) starts halfway down page 8.
- The explanation of Figure 5 (on page 7) starts on page 4.
- Figure 4 (on page 6) is not discussed until Section 2.2 on page 10.

Pages 8 and 9 would also be easier to read with some paragraph headings indicating which part of the algorithm is being discussed.

Other comments: First, the discussion on page 1 gives the impression that unification has never been studied in a generic or abstract fashion, although later you make it clear that it has. I appreciate that this is to motivate the problem, but maybe you could be less forceful about it?

I suggest clearly stating once in prose what "Miller's pattern fragment" is given that it is the topic of the paper. Many readers will know, and the paper does define the pattern fragment (e.g. in Figure 1) but never directly connects this definition to the phrase "pattern fragment."

Citations are formatted strangely throughout the whole paper, e.g. "such as Dunfield and Krishnaswami Dunfield and Krishnaswami [2019]" (L25).

I found the definition of GB-signature confusing until I got to the examples in Section 7. Your notion of "arity" in the STLC includes the sorts of the inputs _and_ the output of a function symbol, but to me this doesn't square with the terminology of an arity as a "variable context." It might help to give the examples earlier on, closer to where GB-signatures are defined.

Typos:
- L6: "proved on papers"
- L172: "is actually arises"
- L173: This sentence is duplicated with a few words changed on L289.
- L234: the second premise of the rule should read $\Delta_1$ not $\Gamma$
- L347: "additional the"
- L626: "on which the algorithm relies on"
- L741: Property 3.17 should say "...for pattern-friendly GB-signatures."

Questions to be addressed by author response
--------------------------------------------
- Can you clarify exactly which aspects of the paper are novel, besides the notion of GB-signature? For example, would you say there is anything novel in Section 2.1?
- Rather than taking the category of renamings as the input to your framework, could you instead consider the entire category of substitutions, of which the renamings form a subcategory? (In particular, the paper "Relative induction principles for type theories" by Bocquet, Kaposi, and Sattler isolates a universal property for the subcategory of renamings, so it seems to me possible in theory.)



Review #265B
===========================================================================

Overall merit
-------------
A. Strong accept: I will argue for acceptance.

Reviewer expertise
------------------
Y. Knowledgeable: I am knowledgeable about the topic of the paper (or at
   least key aspects of it).

Summary of the paper
--------------------
This paper presents an implementation of second-order unification of lambda-calculus terms in Agda, using Miller's pattern fragment. It then generalises this to an arbitrary signature in a particularly neat way, showing how the generalisation can express unification in many other settings.

Assessment of the paper
-----------------------
I am impressed by how neat the generalisation of unification is. Very few special-purpose structures are introduced: renaming of terms is functorality of arities, metavariable applications are unified by pullbacks, etc.

The treatment of failure in Remarks 2.2, 2.3 is particularly elegant - it is very nice to have a definition of mgu that does not have a side-condition of solvability.

Although the paper never claims to, I was constantly expecting unification modulo β-equivalence to appear, because (a) in dependently typed language implementation, Miller's pattern fragment is often used for this purpose, and (b) the main example is the λ-calculus. I suspect I will not be the only reader misled in this way, so please state explicitly in the introduction equations between terms are out of scope.

Getting LaTeX to lay out figures well is always annoying, but the positioning and ordering of figures in this paper is particularly bad. The main text introduces figures in the order 1, 5, 2, 3, 6, 7, 8, 4. I read them in roughly this order, constantly flicking back and forth to match code to text. Please rearrange these!

Detailed comments for authors
-----------------------------
l.6: "on papers" --> "on paper"

l.105: Please explain on first use that ⌊_⌋ and ⊥ are the introduction forms for Maybe

l.335: This paragraph seems to be in the wrong order? It ends with what looks like a definition of metavariable substitutions, which should come first.

l.475: Is the year in Aczel (2016) correct? The bibliography entry is confusing.

l.493, l.591: The text is careful to specify "small category" but the Agda definitions use level-polymorphism to support arbitrarily large universes. As far as I can tell no use is made of this, so might it not be simpler to use small concrete Set levels (i.e. Set, with Set₁ where required)?

l.988: I am in general very sympathetic to the idea of using Agda as a programming language and doing the proofs on paper. (For one thing, it makes it possible to actually read the resulting Agda code!). However, for the specific case of proving termination of unification, would it be possible to adapt McBride's elegant expression of unification in a structurally recursive manner? (See "First-order uniﬁcation by structural recursion", McBride, 2003, and also the later work "A tutorial implementation of dynamic pattern unification", Gundry & McBride, 2012)



Review #265C
===========================================================================

Overall merit
-------------
B. Weak accept: I lean towards acceptance.

Reviewer expertise
------------------
Y. Knowledgeable: I am knowledgeable about the topic of the paper (or at
   least key aspects of it).

Summary of the paper
--------------------
The paper implemented a generic second-order pattern unification algorithm in Agda. It also provides an on-paper category-theoretic proof about its correctness.

Assessment of the paper
-----------------------
The paper is well-written and the Agda code is elegant. The key insight that unification (for the discussed fragment) is _all_ about coequalizers and pushouts (or equivalently finite connected colimits) and injectivity is inspiring.

The only disappointment (if any) would be that the correctness proof has not been mechanized in Agda. In particular, the Agda version of `isFriendly` does not contain the properties needed for the correctness proof (discussed on lines 631-632). I believe it would have been a stronger paper if those properties are also mechanized in Agda (so that no one can use the Agda code incorrectly) along with the correctness proof.

Nonetheless, the current submission still looks impressive. My main reservation is that I am not familiar with the literature on unification so I decided to give Weak Accept.

Detailed comments for authors
-----------------------------
Minor points on typesetting: please use `\citep` when appropriate so that citations do not mix with the surrounding text. (Note: the strange citation formatting was also complained by Reviewer A, and `\citep` is the solution.) Also, the footer on page 5 strangely went into the framed box.



Review #265D
===========================================================================

Overall merit
-------------
C. Weak reject: I lean towards rejection.

Reviewer expertise
------------------
X. Expert: I am an expert on the topic of the paper (or at least key
   aspects of it).

Summary of the paper
--------------------
The paper gives a reconstruction of pattern unification via category theory. In particular, it focuses on second-order pattern unification where meta-variables are applied to distinct bound variables of base type. The goals is to formulate unification algebraically/categoy theoretically and obtain a generic description where we abstractly characterize the context of meta-variables, contexts of bound variables and operations such as pruning, etc. This would then make it easier to customize this abstract framework to different languages such as STLC, System F, etc. 

The paper develops the pattern unification algorithm in Agda and proves termination of the algorithm on paper.

Assessment of the paper
-----------------------
There are four main concerns about this paper:

1) The paper lacks a discussion of how other formulations of higher-order pattern unification algorithms relate to the given implementation in Agda. Fundamentally, there are no new ideas in the formulation of the pattern unification algorithm. The main new part seems to be its particular formulation and implementation in Agda.

  The characterization of meta-variables together with their arity, describing pruning with respect to a vector of bound variables and intersections of bound variables is already present in Dowek's work [2]. It was given a logical foundation through contextual types where contextual types characterize meta-variables of type A in a context Psi [4,5].  The length of Psi is essentially the arity. The higher-order pattern unification was for example described in detail (including pruning/intersections/etc. together with proofs that pruning is correct) in Pientka's PhD thesis (2003), but also in [1]. 

[1] A. Abel and B. Pientka, Higher-Order Dynamic Pattern Unification for Dependent Types and Records, TLCA 2011

[2] Gilles Dowek, Thérèse Hardin, Claude Kirchner, Frank Pfenning, Unification via Explicit Substitutions: The Case of Higher-Order Patterns. JICSLP 1996: 259-273

[3] Jason Z. S. Hu, Brigitte Pientka, Ulrich Schöpp:
A Category Theoretic View of Contextual Types: From Simple Types to Dependent Types. ACM Trans. Comput. Log. 23(4): 25:1-25:36 (2022)

[4] A. Nanevski, F. Pfenning, B. Pientka, Contextual Modal Type Theory, TOCL 2008

[5] A. Nanevski, B. Pientka, F. Pfenning: A modal foundation for meta-variables. MERLIN 2003

[6] B. Pientka, Tabled Higher-Order Logic Programming, CMU PhD Thesis, 2003


  One might say that the main new novelty is the category theoretic treatment of metavariables; but work by Hu et al already does give a category theoretic model for contextual types. So, the main contribution seems the re-formulation / implementation of the actual pattern unification algorithm. This seems a fairly narrow contribution.

2) Treating meta-variables without their type and just keeping the arity lacks / drops information.  For example, there is no distinction between a meta-variable  M arity 0 (but with type A -> B)  and a meta-variable N arity 1 of type B (where the argument takes in one variable of type A) on the syntax level. For example,

Let M be a meta-variable of type A -> B with arity 0. Then the following should succeed (but I don't think that the algorithm does at the momen):

M:0 ; 1 |- M() 1 = 1    since we instantiate M() with the identity function.

In general, we could require that a meta-variable M of type A -> B with arity 0 is lowered to a meta-variable N of type B and arity 1 by instantiating M with \x. N(x). This is in fact what Dowek et all call pre-cooking and is also the restriction imposed in Abel, Pientka's work  where we require that all meta-variables are lowered. I am missing a discussion of what assumptions are made about the syntax of terms (e.g. meta-variables must be always lowered).
In fact, one  nice aspect of contextual types, i.e. keeping the types around when we characterize meta-variables, is that we can give a purely logical account of lowering / raising, i.e. we can justify them by lemmas.

the algorithm would unify:

M:1 ; 1 |- M(1) = \x. c x 2    (or to write it with concrete bound variables)  M:A ; y |- M(y) = \x. c x y

even if M would have type B (base type) with arity 1 (i.e. it may depend on a variable x:A), but it should actually fail, because both sides do not have the same type. 

The current paper should discuss assumptions on terms that are being unified and clearly spell out how raising/lowering can be justified in their framework. If the assumption is that terms are well-typed to begin with, then it should be spelled out and explained how substitutions for meta-variables preserve well-typedness. 

3) The authors claim that their set-up should scale to dependent types. However, I am somewhat doubtful that there is enough information. In the dependently typed setting, it is actually difficult to prove that when pruning a term M (of type A in a context Psi) with respect to variables x1, ... xn  = Phi results in a valid well-typed term M' that is well-typed in Phi -- to put it differently, we could have pruned a variable from Psi which would render the sub-context Phi to be ill-typed/ill-formed. This is discussed in Abel and Pientka's work (see also Pientka's PhD thesis). Therefore, I have doubts that the given description would scale to dependent types without tracking more information than just arity.


4) Motivation: In general, I can see that a category-theoretic reconstruction of pattern unification is intrinsically interesting; but at the same time, I did not find the given explanation convincing (i.e. we can embed STLC / System F into the GB signature and we want a generic unification algorithm for all these systems). We know that we can encode STLC and System F into a lambda-calculus such as LF or Church's simple type theory. We also have pattern unification algorithms for LF / Church's simple type theory and then we simply re-use that algorithm. It is easy to also extend the encoding of STLC with for example de recursive types -- this is done all the time in LF / HOAS style systems. So in some sense unification for LF / Hoas-style systems is already generic and they also have been extended to linear LF (see [6]) -- maybe I am misunderstanding the point the authors want to make. 

[6] Anders Schack-Nielsen, Carsten Schürmann:
Pattern Unification for the Lambda Calculus with Linear and Affine Types. LFMTP 2010: 101-116


Overall, this work could be made more accessible and more stronger by putting this line of research within the existing context of work on pattern unification which arguably takes a syntactic rather than a category-theoretic approach.

Questions to be addressed by author response
--------------------------------------------
Please explain your assumptions on terms; in particular, how you handle the (counter) examples given under 2.
