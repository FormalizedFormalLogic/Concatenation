# Coding conventions

Concatenation follows **Foundation's contribution guidelines**: [`index.md`](index.md),
[`style.md`](style.md), and [`refactoring.md`](refactoring.md) in this directory are copied
verbatim from the `contribute/` directory of
[Foundation](https://github.com/FormalizedFormalLogic/Foundation/tree/master/contribute),
under its Apache-2.0 license:

- [`index.md`](index.md): the flow to the main branch, PR titles and the commit convention,
  pre-submission checks, disclosure of AI involvement.
- [`style.md`](style.md): proof style, naming of intermediate steps, comments and docstrings,
  citations, `grind`, no `sorry`, `set_option`.
- [`refactoring.md`](refactoring.md): priorities and rules for writing and refactoring proofs.

Those documents are the authority; Concatenation follows them as written. This file does not
restate them; it records only where Concatenation differs or adds. Where the two conflict,
Foundation's guidelines win, and the conflict is reported in an issue — with one standing
exception: [`style.md`](style.md)'s citation rule requires a docstring to say so and explain why
when a definition or theorem has no source; AGENTS.md's "Cite the source" rule instead has such
a declaration omit the docstring outright, unless a genuinely useful statement-level explanation
remains. AGENTS.md's rule wins here. When the Foundation pin is bumped, re-copy the three files
above in the same PR if they changed upstream.

Where they say "Foundation", read "Foundation, and Concatenation"; where they name
Foundation-specific files (`Foundation.lean`, `references.bib`, `just` recipes), the
counterparts here are the ones named below.

The reason is practical: material developed here is meant to move into Foundation without a
rewrite, so it is written as if it were already there.

## Concatenation-specific additions

- **Module system.** Every file opts into the Lean module system exactly as Foundation does:
  it starts with `module`, imports are `public import`, and the module docstring precedes
  `@[expose] public section`.
- **Root module.** `Concatenation.lean` imports every module and is regenerated with
  `just mk-all` (`lake exe mk_all --lib Concatenation --module`); CI checks it.
- **Linters.** The library builds with Mathlib's standard linter set, which `lakefile.toml`
  opts into wholesale (`weak.linter.mathlibStandardSet`), minus the header linter; `autoImplicit`
  is off, as in Mathlib. A warning is an error: CI and the pre-push hook build with
  `lake build Concatenation --wfail`. Fix a warning, never suppress it.
- **Citations.** The bibliography is [`references.yml`](../references.yml) at the repository
  root, written in [Hayagriva](https://github.com/typst/hayagriva) YAML rather than
  Foundation's BibTeX `references.bib`; there is no `bibtool` step, the file is edited by
  hand and kept sorted by key. Its keys are the citation keys (`Grz05`, `GZ08`, `Vis09`, …), cited at the end of the docstring in Foundation's form, one line per key:
  ```
  - [Grz05, §3]
  - [Vis09, Theorem 4.3]
  ```
  A key appears at most once in a docstring: results from the same reference go on one line,
  separated by commas, never on one line each:
  ```
  - [Mur22, §3, Lemma 1]
  ```
  A key used in a docstring must have an entry in `references.yml`; add the entry in the same
  pull request.
- **No `sorry`; unproved statements are axioms.** Foundation's guidelines forbid `sorry` in
  finished work. Concatenation forbids it outright, including in the statement-only stage of
  [`workflow.md`](workflow.md): a statement that is not proved yet is declared as an `axiom`
  under the name its theorem will keep, and recorded in [`forgive.yml`](../forgive.yml)
  forgiving that name. The reason is legibility of the audit — an `axiom` is reported under its
  own name, so the report says which unproved results a declaration leans on, where every
  `sorry` collapses into one anonymous `sorryAx`. Proving the statement turns the `axiom` into a
  `theorem` and deletes its entry; a `sorry` that would sit inside a proof becomes its own named
  axiom for the fact it stands for.
- **An `axiom` can silently drop a hypothesis.** Lean pulls a `variable`-bound instance argument
  into a declaration only when the declaration's own type mentions it; an `axiom` has no body to
  mention it indirectly, so a hypothesis like `[U.Δ₁]` or `[𝗜𝚺₁ ⪯ T]` can vanish from the type
  without any error — the resulting statement is *stronger* than intended, and neither
  `lake build`, `just axiom-audit`, nor `just mk-all` catches it. This has happened in
  [AlphaCentauri](https://github.com/FormalizedFormalLogic/AlphaCentauri) (its PR #107, fixed in its
  PR #112). A `statement-formalized` PR must run `#check @Name` on every `axiom` it adds
  and confirm the printed type keeps every intended hypothesis.
- **Open problems are stated with `open_problem`, never as axioms.** An `axiom` is reserved for a
  known theorem awaiting formalization: a statement of unknown truth may be false, or contradict
  a known theorem together with another one. `open_problem Name := p` (from
  `Concatenation/OpenProblem.lean`) declares `def Name : Prop := p` and records it, so that
  `just open-problems` lists it, with its docstring, on the project's pages; it is not listed in
  `forgive.yml`. `Name` is the name the theorem would carry, following the naming of theorems
  (`essentiallyUndecidable_TC`), so that proving it
  keeps the name. The docstring is mandatory and asks `p` as a question (`Does
  $\mathsf{WTC} + \mathrm{TC3}$ interpret $\mathsf{TC}$?`), then cites the source; it does not say
  that the problem is open. A result that depends on an open problem takes it as a hypothesis
  `(h : Name)`.
- **No `axiom` or `open_problem` in a `Basic.lean`.** As a rule, a `Basic.lean` holds only the
  definitions of its subject and the facts proved about them, which every other module of the
  subject imports. An `axiom` or an `open_problem` goes in a module of its own, or in the module
  of the results it is about, never in `Basic.lean`.
- **Reuse before restating.** Foundation's theories, notations, definability classes, and the
  hierarchy are the vocabulary. A definition that duplicates a Foundation definition under a
  new name is rejected in review. If Foundation's API is missing or awkward, say so in the
  issue you are working on rather than working around it; a human takes it upstream.
- **A formula defining a relation is tied to it by a definability instance.** Do not pair a
  formula with a hand-written `eval_` lemma (`M ⊧/![x, y] φ ↔ R x y`) and its relatives: state
  that the formula defines the relation or function with Foundation's definability classes, as
  Foundation itself does, and let `simp` use the instance. An arithmetic formula is a
  hierarchy-classified `𝚺ᴬ₀.Semisentence k` (or `𝚺ᴬ₁`, …) built with `.mkSigma`, followed by
  its `Defined` instance and the `Definable` instance derived from it, named as in Foundation's
  arithmetic (`fooDef`, `foo_defined`, `foo_definable`):
  ```
  def isRegularDef : 𝚺ᴬ₀.Semisentence 1 := .mkSigma “y. 0 ≤ y ∧ ∀ v < y, v + 1 ≤ y”

  instance isRegular_defined : 𝚺ᴬ₀-Predicate[V] IsRegular via isRegularDef := .mk fun v ↦ by
    simp [isRegularDef, isRegular_iff, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
      Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]

  instance isRegular_definable : 𝚺ᴬ₀-Predicate[V] IsRegular := isRegular_defined.to_definable
  ```
  The bracketed model in these notations expands to the named argument `(V := V)`, so the model
  variable is called `V`. A formula whose quantifiers or parameters keep it out of every
  hierarchy class uses the unclassified `ℒₒᵣ-relation[M] R via φ`. A formula of another language
  without a hierarchy notation is tied to its relation the same way with the unclassified
  classes, `ℒ⌢-relation[M] R via φ` and `ℒ⌢-predicate[M] P via φ`, as Foundation's set theory
  does for `ℒₛₑₜ`. A lemma that computes a formula's value only under extra hypotheses stays a
  lemma.
- **`<|` for low-precedence application.** Write `f <| x`, not `f $ x`, and prefer it to
  parentheses whenever the argument runs to the end of the term: `exact Or.inr <| Or.inl h`, not
  `exact Or.inr (Or.inl h)`. Foundation's guidelines do not choose between the two spellings;
  Mathlib's `style.dollarSyntax` linter does, and this repository follows it.
- **Attributes on their own line.** An attribute goes on the line above the declaration it
  marks, never in front of it on the same line, so that it does not lengthen the header:
  ```
  @[simp]
  lemma card_empty : …
  ```
  not `@[simp] lemma card_empty : …`. The same holds for modifiers after the attribute
  (`@[simp]` above `private lemma …`) and for `@[inherit_doc]` above a `notation`; only
  `@[expose] public section` stays on one line.
- **Avoid `?_`.** Prefer `apply f` to `refine f ?_`, and a direct term to a `refine` with holes;
  [`style.md`](style.md)'s preference for direct term construction is the same rule seen from the
  other side. `use` takes data only — a witness of a `Type`, never a proof of a hypothesis: split
  what remains with `and_intros` rather than passing the proof to `use`.
- **A declaration header takes as few lines as fit.** A header that fits within the
  100-character line limit is written on one line,
  `noncomputable def interpretation : Interpretation T U where`, not with its type
  broken onto a second line. A header too long for one line is broken as late as possible, each
  line filled up to the limit, with continuation lines indented four spaces.
- **AI disclosure.** As in Foundation: every commit carries a `Co-Authored-By` trailer for the
  model, and the PR body says an AI agent wrote it. Here that is the normal case, not the
  exception, so every PR body says so explicitly.

## Standards from Foundation's review

Foundation's maintainers have reviewed the AI-assisted pull requests sent there; the points they
settled on are collected here, since material written here is meant to pass the same review. The
pull request that raised each point is given as `Foundation#n`. Where Foundation's guidelines
above already say the same (no `maxHeartbeats`, `grind` for routine steps), they are not repeated.

**Statements**

- **`∀`, not `¬∃`.** A result saying that no object has a property is stated as
  `∀ x, ¬P x` (or with the positive conclusion it yields), not `¬∃ x, P x`, so that users need no
  `push_neg` (Foundation#900).
- **The strongest natural form.** State `Primrec` rather than `Computable` when it holds
  (Foundation#900); state provability over the weakest base theory that suffices, `𝗜𝚺₁ ⊢ σ`,
  rather than over an arbitrary `T` with `[𝗜𝚺₁ ⪯ T]` (Foundation#902); drop hypotheses the proof
  does not need (Foundation#906); generalise where it costs nothing, e.g. a parameter type `ξ`
  or arity `n` instead of a fixed one (Foundation#902, Foundation#906).
- **Constructions, not existence.** When a witness — a formula, a bound, a function — can be
  written down, define it rather than prove that it exists; an existence statement used over
  and over is turned once into a (possibly noncomputable) function (Foundation#902,
  Foundation#903, Foundation#1018).
- **No lemma that only restates what is at hand.** A lemma that follows from a structure's field
  or from `simp [def, models_iff]`, or whose witness is the obvious one, is not stated; state the
  property that carries content instead (Foundation#1041).

**Definitions**

- **A formula carries its class.** A formula known to lie in a hierarchy class is typed by it,
  `𝚺ᴬ₀.Semisentence k`, rather than given a separate `hierarchy_foo` lemma (Foundation#902); its
  relation is tied to it by definability instances, as described above (Foundation#902,
  Foundation#1062).
- **No definition without a second use.** No auxiliary definition for a transitory
  representation (`Theory.codes`; use the standard bridges such as `Computable.encode_iff`,
  Foundation#905), no function defined for a single use (Foundation#901), no structure or type
  class with a single instance in practice (Foundation#906), and no `abbrev` that only re-spells
  a type (`ArithmeticBoundedSemiformula` for `ℬ[<, ℒₒᵣ].Semiformula`, Foundation#959).
- **Existing notation over new notation.** Use `insert`, `LogicalConnective`, heterogeneous
  notation and the like instead of local or scoped notation of one's own (Foundation#903,
  Foundation#906).
- **The coding stays opaque.** Constants of the coding (`eqIndex`, `addIndex`, …) are not
  unfolded to their values, and an argument assumes no more of a coding than that it is
  $\Sigma_1$- or $\Delta_1$-definable (Foundation#903, Foundation#1018).
- **Names and argument order.** Predicates are adjectival, like `Provable` (`…Satisfied`,
  `…True`); a name does not repeat its namespace (`Bounding.Hierarchy`, not
  `Bounding.BoundingHierarchy`), and a structure parametrised by `ℬ : Bounding L` lives in
  `Bounding` so that it reads `ℬ.Semiformula` (Foundation#838, Foundation#959, Foundation#1018).
  Arguments follow `Semiformula.Eval`: parameters before the formula (Foundation#1018).
- **Models are called `V`.** The type of a model is `V` (a second one `W`), as in Foundation's
  arithmetic, whose hierarchical definability notations expand to `(V := V)`.

**Proofs**

- **Model theory with predicates, not formulas.** An argument inside a model works with
  predicates on the model and their definability, not with formulas and `⊧/`: an axiom scheme is
  connected to its models only through a lemma of the shape of `InductionOnHierarchy.succ_induction`,
  and induction runs over definable predicates (Foundation#929). Syntactic operations
  (`Rew.q`, `Rew.subst`, `emb`) stay out of such proofs and out of downstream statements; the
  usual route is syntax, then model, then syntax, as in ProvabilityLogic's `SolovaySentences.lean`
  (Foundation#902, Foundation#929).
- **The meta level uses `⊢`.** A statement about provability outside the model uses `T ⊢ σ`,
  not the internalised `Proof` of the bootstrapping (Foundation#900, Foundation#903).
- **Reuse, do not reprove.** A result already in Foundation or Mathlib (`REPred.or`,
  `computablePred_iff_delta1`, `piOne_downward_absolute`, `by definability`) is used, or
  specialised, not proved again (Foundation#903, Foundation#905, Foundation#1043).
- **Fold one-off lemmas.** An auxiliary lemma used once is folded into the proof that uses it
  or made `private` (Foundation#901, Foundation#906).
- **Shape of proofs.** A long proof is not an anonymous constructor of tactic blocks
  `⟨by …, by …⟩`; use `constructor` (Foundation#838). A routine case analysis is closed by
  `grind`, `omega` or `simp` rather than a chain of `rcases` and `exact ⟨…⟩` (Foundation#900).
  Mathlib's deprecations are followed (`Std.Refl`, `Std.Symm` for `Reflexive`, `Symmetric`,
  Foundation#834), and no comment excuses a linter: rewrite until it is satisfied
  (Foundation#901).

**Organisation**

- Generic lemmas go to the module where they belong, not next to their first use
  (Foundation#850, Foundation#858, Foundation#900); here, `ToMathlib/` or `ToFoundation/`.
- The definitions of axioms and schemes are kept together; proofs that they are equivalent go in
  a file of their own (Foundation#921).

## Checks before opening a pull request

```bash
lake build Concatenation --wfail   # no errors and no warnings
just axiom-audit                   # no axiom outside the allowlist, except what forgive.yml forgives
just no-sorry                      # no `sorry` in the sources, no `sorryAx` in forgive.yml
just mk-all                        # Concatenation.lean up to date
```

A `statement-formalized` PR additionally runs `#check @Name` on every `axiom` it adds — see
"An `axiom` can silently drop a hypothesis" above.
