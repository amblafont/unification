POPL 2025 Paper #103 Reviews and Comments
===========================================================================
Paper #103 Semantics of pattern unification


Review #103A
===========================================================================

Overall merit
-------------
3. Weak accept

Reviewer expertise
------------------
2. Some familiarity

Paper summary
-------------
The goal of the paper is to develop a uniform semantics for a class of
unification problems for a variety of different languages
with metavariables.   In particular, the paper focuses on pattern
unification, that is, unification problems where metavariables are only
applied to distinct object variables. 

To demonstrate its approach, the paper proceeds in two steps.  The first
step is an exposition of an algorithm (and its Agda implementation) for
pattern unification for an untyped lambda calculus with metavariabless.
The algorithm is organized carefully around a case analysis. Three cases
stand out: (i) unification of two metavariable applications; (ii)
unification of so called rigid terms (such as two lambdas or two apps);
and (iii) pruning of rigid terms.  The second step is the generalization
of the algorithm  beyond the setting of untyped lambda calculus. This
involves abstracting over syntax with the use of an abstract specification
for a language that the paper calls GB-signatures, and that consists of an
  abstraction of the rigid operations of the language, their arities (and
  renamings between them) and scopes. The paper describes these
  abstractions as category theory constructions. Given these
  constructions, the paper revisits the algorithm and shows that it can be
  phrased in an abstract way by casting the object-syntax-specific
  handling of the three cases above in category theory terms: case (i)
  amounts to the use of equalisers and pullbacks, case (ii) requires
  checking the equality of the names of rigid operations, and case (iii)
  involves inverse renaming.  The third step is the proofs that the
  general algorithm is sound, terminating and complete. These proofs rely
  on a few conditions that entail properties of the GB-signatures such as
  that the category of arities has equalizers and pullbacks. When a
  language with metavariables corresponds to a GB-signature with these
  properties it is called pattern friendly.

To demonstrate the applicability of pattern friendly languages, the paper
presents a series of lambda calculi as use cases that fit its framework.

Comments for authors
--------------------
Even though I have just elementary knowledge of category theory, I enjoyed
reading the paper and I believe I understand now unification in a deeper
way than I did before. Despite a deep dive in category theory from the
get-go, the paper is well-written. In particular, the use of the concrete
untyped lambda calculus example to introduce the key ideas prior to the
generalization was particularly helpful. Section 3, 4, 5, and 6 are pretty
hard to penetrate for someone who is not well-versed ideas but I was still
able to extract the key points. Section 7 helped a lot to understand how
the general setting can be made concrete in different ways (for example
how the arities category can encode a variety of information) 

That said, I have struggled to identify the novelty of the paper. The
general idea of viewing unification  through the lens of category theory
and, in particular the role of equalizers and pullbacks, is not new ---
the first time I encountered it was when studying the Rydeheard and
Burstall text book as a grad student, which the paper also cites.
Similarly, the organization of the algorithm for pattern unification
around the presented case analysis is not new. For instance, the short
Vezzosi and Abel paper that this paper cites has a similarly structured
algorithm modulo \alpha, \beta and \eta equivalence, uses equalizers and
pullbacks to express it in categorical terms, and points to the use of
Indexed Containers as a way to abstract over the object-level details of
the language operators. 

Based on the above, my conclusion is that the novelty of the paper is (i) the
GB-signatures, the identification of the conditions for pattern-friendly
languages and the demonstration of the applicability of this formulation
in section 7; and (ii) the proof of correctness for pattern-friendly
languages. 

I do not have the expertise to comment on whether the above
is a sufficient contribution and/or requires overcoming significant
technical hurdles.

However, I think that independently of the magnitude of its contributions,
the paper is missing two things: 

(i) A detailed discussion of limitations. There are some hints here and
there about what the framework can handle or can not, but the paper should
devote some space to explain what GB-signatures can and cannot do in
detail and how hard it is to prove the conditions expected for pattern
languages. 

(ii) A detailed discussion of motivation. While unification is undoubtedly
important, it has been studied for decades, and there is a plethora of
formulations and proofs of correctness in the literature for specific
contexts. In particular, there is a lot of work that covers the
applications of unification in PL and a lot of work that discusses how to
correctly extend the unification capabilities of existing language. The paper should
place its results in this context and explain why the proposed
generalization is significant. A possible argument could be that it
facilitates the correct extension of existing languages, but the paper
should spell it out and argue that prior work does not cover this need
already.  



A few typos
===========

line 37: ``rule'' --> ``rules''

line 108: missing ``the'' before ``endofunctor''

line 114: ``consists in'' --> ``consists of''

line 92: the abbreviation mgu has already been introduced

line 635: redundant ``be'' after ``must''



Review #103B
===========================================================================

Overall merit
-------------
3. Weak accept

Reviewer expertise
------------------
3. Knowledgeable

Paper summary
-------------
Higher-order pattern unification  (HOPU) is a subproblem of higher-order unification (HOU) discovered by Miller in which metavariables have to be applied to distinct bould object variables.  It is decidable and has most general unifiers (unlike HOU in both respects).  This paper proposes a generalization that abstracts over both the constant/function and variable/binding structure of the object language, and the notion of metavariable whose uses are constrained in a way that allows for the idea of the hhigher-order pattern unification algorithm to still work.  The first two sections present an overview of the ideas and illustrate the approach using the specific case of ordinary HOPU and the proposed generalization (though with many details deferred till later), using Agda and on-paper inference rule style.  Sections 3-6 present the formal details, identifying suitable categorical structures to abstract over binding signatures and the required associated operations to make such a signature "pattern-friendly", and then showing soundness, termination and completeness (which follows from the first two since soundness incorporates the most general unifier property).  Section 7 presents further examples that are said to be instances of the framework, thouhg again at a high level, includign patterns where metavariables are applied to sets of variables, lambda calculus with types and with beta-normal eta-long forms, System F, and an ordered linear calculus with both unrestricted and ordered-linear variables.

Comments for authors
--------------------
Evaluation

I think this paper presents a significant contribution, because traditionally higher-order pattern unification has seemed like a rather syntactically motivated special case of higher-order unification without a very strong semantic basis or justification, but it is so useful in practice (cf. Abella, various LF-based systems, etc.) that it is compelling to have a stronger justification for it aside from the fact that it seems to work well in practice as a special case of HOU.  This paper defines a space of signatures of languages with a notion of pattern which can be instantiated in many ways.

However some aspects of the presentation choices and detail sometimes get in the way of appreciating or understanding this work.  For example, given that the formalization later in the paper focuses on the rule-based systems, I am not sure how much the Agda implementation adds - it is not a complete formalization even of properties like termination, although it does help to use dpeendent types to ensure some basic well-formedness checks.  This is ultimately a stylistic choice and as a not very Agda-literate person I may not be representative of the subset of the POPL community of people likely to be interested in this kind of work.

I also found myself wondering about relation to some work tha thas a similar feel (without the categorical semantics aspect) such as by Pottier & Poulliard (ICFP 2010/2011/JFP 2012) and perhaps Gundry et al.'s work on typ inference (which includes unification as a subproblem), see particularly Gundry's thesis which presents a reconstruction of Miller's higher order pattern unification (ch 4).  I also wondered about whether mixed-prefix unification (Miller 1992) would be definable as an instance of this approach (whehter for first or higher order patterns).  So, I feel the context and relationship of this work to prior work could probably be strengthened somewhat.

I think the presentational issues may be possible to remediate as part of a revision but the current state of the paper requires quite a lot of effort (flipping back and forth and guessing missing details / giving benefit of the doubt).  So I would be open to conditional acceptance if other reviewers that have apropriate expertise agree that the formal content of the paper is sound.

Detailed comments

In my review the markdown means: please insert **this**, please delete ~~that~~, please spellcheck _this_.

6: Lawvere theories are mentioned here but not in the rest of the paper, can it be explained what corresponds to Lawvere theories here (e.g. GB signatures/their initial algebras)?

9: missing "and" before "(intrinsic)"

29: the justmgent for unification here with $t,u$ doesn't seem to be used much later, instead $t=u $ is used.

41: The rule for FO does not make much sense to me.  In first order terms, metavariables do not take argumenbts fo m should alkways be zero.  It seems OK to allow multiple object variables (universal/rigid variables) so n could be greater than zero, and need not equal m.  So if we change teh precondition to $m = 0$ and have no constraint on $M$ then the rule on line 71 can be instantiated in this way provided $\mathcal{A}$ is a category whose objects are natural numbers and zero is initial so that the $x \in hom_{\mathcal{A}}(0,n)$ needed in the rule for M(x) in line 71 is uniquely defined.

59: The notation $\mathcal{O}_n$ is not defined here nor until much later in the paper.

172: "_litterature_"

284: Reading figure 2 for section 2.1 I wondered what $-\{x\}$ notaion meant and had to read further to find this.  Consider including the definition of $-\{x\}$ or its signature for self-containedness.

Relatedly, though I see the bottom half of figure 2 mentions section 2.2, I do find it hard to read with this figure and figure 5 placed in the paper well before the beginning of section 2.2 and figures 6/7 which define the alternative versions of Tm and the other notations used in the generalized setting.

296: Figures 4 and 5 where these signatures are used are two pages away.

464: If unify-fles* is syntactically identucal in the generalized case, can it actually be defined once and reused in Agda (perhaps by abstracting over the Tm type and commonPositions/equalizerfunctions somehow?)  If not, I would slightly prefer having the definition repeated since even if the code is the same, the types are different, and the current way the figures are organized means you have to read carefully to realize the version of prune in figure 5 is not called explicitly but instead called in the unify-flex-* function implicitly included form figure 4.

560: It might be helpful to illistrate example 2.5 with Agda code showing how the binding signature specification in figure 6 can be instantiated with - ideally we'd be able to see more concretely how the code in figures 2(top) and 4 falls out by instantiating figures 2(bottom) and 5 respectively that way, currently it is a little mysterious.


622: "then , thus" - extra space before comma

674: in $S = (\mathcal{A},O,\alpha)$ it seems that the $O$ should be $\mathcal{O}$ based on how things are written later.  Also, this section does not make much sense to present before the definitions of GB-signature and pattern-friendly (needed for lemma 3.12) are given in section 3.2 (def 3.13/3.14).

744: Is $J$ in $\int J \to \mathcal{A}$ meant to be $\mathcal{O}$?  If not, what is it?

755: It was easy to find out that finite connected limits exist if and only if all pullbacks and equalizers exist (which makes it clearer whyyou want this); perhaps mention this parenthetically?

775: "**In** the rest..."

804-810: it would be helpful to hoist the definition of $\mathcal{C}$ out of Lemam 3.21 and perhaps parameterize it explicitly on $S$, to make the statements of lemmas 3.22-3.23 self-contained.

805: "hold~~s~~"

827: Please insert words between pathematical statements siuch as between $\Gamma,$ and $x$ and between $\Gamma_1', $ and $\sigma$ to make it easier to split the sentence up.

860: The second $\mathcal{L}x$ on this line should be $\mathcal{L}y$.

863: $(X : N)$ should be $(X : n)$ I think.  

881: "U-RIG **rule**."

971: "empty size" -> "size zero"?

990: the section on termination finishes without a statement of the termination theorem itself

1002: Again as a presentational suggestion, would it be worth considering providing this section earlier, and if possible fleshing it out with the definitions of the GB signatures and pattern friendly operations?  They are described in the text but details for example of how we would accommodate sets as arguments to metavariables, or ordered linear bindings, might help make things more concrete earlier in the paper before the theory development.

1061: I think in the third column the $\Rightarrow should be a  -->> (not sure of the latex macro)

1080: should this be a table (say table 2)?  Later the system f definitions are said to be in table 1, which is on the previous page.

Also, am I right in believing that since the system F syntax is not up to any equational theory / normal form structure, the instantiation as a GB-signature is largely straightforward?  The only unusual aspect is the need to do bookkeeping for two contexts, i.e. A is a product category?

1100: In unifying $M(\vec{x}$ and $M(\vec{y})$ in a typed setting, do we need to check the matching xs and ys have the same types (or are we relying on the type system to have checked this already I guess)?

1150: "denote**s**"


References:

Nicolas Pouillard, François Pottier:
A unified treatment of syntax with binders. J. Funct. Program. 22(4-5): 614-704 (2012)

Nicolas Pouillard, François Pottier:
A fresh look at programming with names and binders. ICFP 2010: 217-228

Nicolas Pouillard:
Nameless, painless. ICFP 2011: 320-332

Adam Michael Gundry:
Type inference, Haskell and dependent types. University of Strathclyde, Glasgow, UK, 2013

Adam Gundry, Conor McBride, James McKinna:
Type Inference in Context. MSFP@ICFP 2010: 43-54



Review #103C
===========================================================================

Overall merit
-------------
2. Weak reject

Reviewer expertise
------------------
3. Knowledgeable

Paper summary
-------------
The paper generalizes Miller's unification on higher-order patterns by taking a
categorical perspective.  The gained generality is exemplified with an ordered
linear lambda calculus and polymorphism.  Other extensions, such as dependent
types, can not be captured with the present approach.  The paper also presents
an implementation of the more general algorithm in Agda, where Agda is used as a
programming language (rather than a theorem prover).  Nevertheless, dependent
types are used to capture some of the invariants of the representation and
algorithm.

Comments for authors
--------------------
The generalization is nontrivial and (as far as I can tell with my limited
categorical background) done well.  However, the motivation remains unclear,
especially in comparison with the (unpublished) [31] which also provides a
categorical approach to pattern unification.  The generalization to the ordered
language makes sense, but is hardly surprising as versions for substructural
pattern unification have previously been devised using syntactic method
(see, for example, Schack-Nielsen and Schurmann [LFMTP 2010]).

For the polymorphic case, it is probably worth mentioning [Pfenning, LICS 1991]
which works for the Calculus of Constructions.  One question I have here:
eta-long forms are not stable under type substitution, so respecting eta
equality requires some care.  From the rather abbreviated presentation in
section 7.5 I couldn't tell whether and how this problem is handled.