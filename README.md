# microgpt-rocq

`microgpt-rocq` is a monolithic Rocq development of a small transformer language-model core with exact rational semantics, machine-checked proofs, OCaml extraction, and a runnable executable.

The repository is centered on [`MicroGPT.v`](./MicroGPT.v). That file contains the model, the proof surface, the extraction commands, and the formal demo values. [`main.ml`](./main.ml) is the executable shell around the extracted artifact. It prints fixed formal demos, exercises extracted training and decoding helpers, and runs a small corpus-driven runtime trainer on top of the verified core. The checked-in corpus lives at [`data/demo_corpus.txt`](./data/demo_corpus.txt). CI proves the Rocq file, regenerates the extracted OCaml, builds the executable, and runs it.

This is not a toy parser dressed up as a model. It is a real transformer language-model core written in Rocq. The model includes token embeddings, positional embedding surfaces, query/key/value projections, causal self-attention, a stacked shared-weight depth controlled by hyperparameters, an MLP block, output logits, normalized token scoring, sequence loss, batch loss aggregation, greedy generation, filtered top-k and top-p decoding, an output-head reverse-mode training path, and a whole-model gradient and optimizer surface that reaches embeddings, attention weights, the MLP, and the output projection.

The semantics are exact and explicit. Scalars are rationals of type `Q`, not floating point values. Attention uses a positive normalized kernel based on `1 + dot(q, k)^2`, and token probabilities come from a monotone positive score map over logits before normalization. Prediction, loss, and filtered decoding all route through that same normalized surface. The point of the formalization is not to imitate a Python training loop instruction by instruction. The point is to define a theorem-bearing transformer core that proves, extracts, builds, and runs.

The proof surface is broad and concrete. `MicroGPT.v` proves the shape invariants across vectors, matrices, attention, transformer blocks, and forward passes; it proves causal prefix discipline; it proves cached attention equal to recomputed attention; it proves hidden-state and batch-interface preservation; it proves the readout gradient and output-head SGD surfaces well-formed; and it proves that the whole-model gradient, batch gradient, SGD step, SGD loop, Adam step, and Adam loop preserve the model or optimizer well-formedness they are supposed to preserve.

The executable has four layers. First, it prints fixed formal demos from the extracted development. Second, it prints a formal output-head training demo and a formal whole-model training and decoding demo. Third, it runs a runtime trainer that freezes the extracted transformer body and trains only the output projection on top of verified hidden states. Fourth, it runs a native float whole-model trainer over the same architecture and scoring rules so the executable has a practical end-to-end training path instead of only a readout-head fine-tune.

Build from a native Linux tree with Rocq 9.0 and OCaml 4.14:

```bash
coqc MicroGPT.v
ocamlopt -c microgpt_extracted.mli
ocamlopt -c microgpt_extracted.ml
ocamlopt -c main.ml
ocamlopt microgpt_extracted.cmx main.cmx -o microgpt_demo
./microgpt_demo data/demo_corpus.txt
```

GitHub Actions runs the same pipeline on every push and pull request. The workflow proves `MicroGPT.v`, regenerates the extracted OCaml, builds the executable, runs it against the checked-in corpus, and checks that the formal and runtime demo surfaces appear in the output.

The executable also supports focused section runs through `MICROGPT_SECTION`. Set it to `formal`, `runtime_head`, or `runtime_full` to run only that part of the program while keeping the default `all` behavior for CI and ordinary execution.
