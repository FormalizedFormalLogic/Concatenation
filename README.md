# Concatenation

Concatenation aims to formalize results on the theory of concatenation, the first-order theory of
strings, built on
[Foundation](https://github.com/FormalizedFormalLogic/Foundation), the Lean 4 library of
mathematical logic of the [Formalized Formal Logic](https://github.com/FormalizedFormalLogic)
organization. It is also an experiment in autonomous AI formalization.

The [website](https://sno2wman.github.io/Concatenation/) gathers the list of open problems and the import graph.

Humans decide what to formalize, one GitHub issue at a time; AI agents write, review and maintain
the Lean code. Every step happens on GitHub. The process is [`docs/workflow.md`](docs/workflow.md),
the contract for agents is [`AGENTS.md`](AGENTS.md), and the code conventions are
[`docs/conventions.md`](docs/conventions.md).

## Building

Nothing here has to be elaborated from source: Mathlib comes from its own cache, and Foundation
and this library from the shared FormalizedFormalLogic build cache, keyed by the revision the
manifest pins. A miss compiles what is missing and is not an error.

```bash
just cache           # Mathlib's, Foundation's and this library's prebuilt artifacts
just build           # the above, then Concatenation
just axiom-audit     # the axiom allowlist
just no-sorry        # sorry-freeness
just hooks           # run the CI checks before every push (needs lefthook)
just import-graph    # the module import graph, as import_graph.{png,pdf,html}
```

## Open problems

The [list of open problems](https://sno2wman.github.io/Concatenation/open-problems/) stated in Concatenation, each declared by `open_problem` with its docstring and references. Its data is generated from the environment by [`OpenProblems.lean`](./OpenProblems.lean) on every push to `main`, and the page is [`pages/open-problems/`](./pages/open-problems); run `just open-problems` to regenerate the data locally. To add a problem, open an issue from the [Open problem template](https://github.com/SnO2WMaN/Concatenation/issues/new?template=open-problem.yml) with its statement and a source.

## Import graph

The import graph of the modules of Concatenation, regenerated on every push to `main`: [PNG](https://sno2wman.github.io/Concatenation/import_graph.png), [PDF](https://sno2wman.github.io/Concatenation/import_graph.pdf), [HTML](https://sno2wman.github.io/Concatenation/import_graph.html).

## Related projects

- [AlphaCentauri](https://github.com/FormalizedFormalLogic/AlphaCentauri): the sibling project on
  first-order arithmetic, whose process and infrastructure this project takes over.
- [Foundation](https://github.com/FormalizedFormalLogic/Foundation): the library this project
  builds on and feeds back into.
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti),
  [TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap),
  [TauCetiReview](https://github.com/TauCetiProject/TauCetiReview): the AI-authored,
  human-directed Lean library whose process this project adapts.

## License

[Apache-2.0](./LICENSE)