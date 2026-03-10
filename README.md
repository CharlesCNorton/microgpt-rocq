# microgpt-rocq

`microgpt-rocq` is a monolithic Rocq formalization of a small transformer-style language-model core with OCaml extraction.

The repository contains:

- a single theorem-bearing Rocq development in `MicroGPT.v`
- a small OCaml driver in `main.ml`
- a small checked-in text corpus in `data/demo_corpus.txt`
- extracted OCaml artifacts generated from the Rocq source
- a GitHub Actions workflow that proves, extracts, builds, and runs the executable

## What Is Implemented

The current model is a compact transformer-style language-model core with attached verified training and generation surfaces.

Implemented pieces:

- token embeddings
- query/key/value projections
- causal self-attention
- shared-weight stacked transformer depth controlled by hyperparameters
- an MLP block
- output logits
- normalized output distributions
- sequence-level token loss
- batch loss aggregation
- greedy autoregressive generation
- next-token prediction by argmax
- a linear readout head over the final hidden state
- squared loss for the readout head
- a reverse-mode backward pass for the readout head
- a proved output-head SGD update over causal hidden states
- a proved repeated output-head training loop inside the Rocq development
- a whole-model reverse-mode-style gradient surface inside the Rocq development
- whole-model SGD updates over embeddings, attention weights, MLP weights, and output projection
- an Adam-style optimizer state inside the Rocq development
- in-core temperature scaling plus top-k and top-p filtered decoding surfaces
- extracted OCaml exports for the whole-model loss, gradient, SGD, Adam, and decoding helpers
- formal token encoding and decoding helpers for the demo vocabulary
- a frozen-body output-head training loop in the OCaml executable
- deterministic and sampled generation paths in the OCaml executable
- optional file-backed runtime corpus loading for the OCaml training demo

Scalars are exact rationals (`Q`), not integers. Attention uses the positive kernel

`1 + dot(q, k)^2`

followed by explicit normalization by the prefix score sum. This keeps the attention step exact while making it materially closer to a true normalized weighting scheme than the earlier unnormalized integer baseline.

Token probabilities are derived from a monotone exact positive score map over
logits: nonpositive logits use a reciprocal branch `1 / (1 - x)`, while
positive logits stay linear as `1 + x`. Greedy prediction, token loss, and
top-`k` / top-`p` decoding all route through that same normalized surface.

## What Is Proved

`MicroGPT.v` proves:

- vector and matrix shape preservation
- attention output shape preservation
- causal prefix invariance for attention
- cached attention is extensionally equal to recomputed prefix attention
- transformer block shape preservation
- forward-pass output shape preservation
- batch interface length preservation
- greedy generation length preservation
- final hidden-state shape preservation
- readout gradient shape preservation
- explicit reverse-mode gradient formulas for the readout head
- output-head gradient shape preservation over batches of causal hidden-state examples
- output-head SGD preserves model well-formedness
- concrete properties of the three demo models

The whole-model training and optimizer additions in the current file are executable
and monolithic with the rest of the formalization. The strongest proof coverage
still sits on the structural and output-head training surface. The extracted
runtime now also exposes a concrete whole-model demo surface for full-model
gradient evaluation, one-step SGD, top-k and top-p decoding after training, and
an Adam-side prediction checkpoint.

## Demos

The extracted executable prints three concrete model runs:

- `demo1`: a nontrivial rational-attention run
- `demo2`: a simple single-token run used for the verified readout-loss example
- `demo3`: a second simple run with a different output projection profile

The executable also prints:

- a short greedy continuation for `demo1`
- an encoded sequence loss for `demo1`
- an encoded batch loss for `demo1`
- the encoded squared loss for the `demo2` readout example
- the encoded reverse-mode gradients for the readout weights
- the encoded reverse-mode gradient for the readout bias
- a formal output-head training demo extracted from the Rocq development
- a formal whole-model training and decoding demo extracted from the Rocq development
- a runtime training demo over a tiny token corpus
- a before/after loss trace for a cold output head trained against extracted hidden states
- before/after greedy continuations for the trained output head
- before/after sampled continuations for the trained output head
- before/after top-p sampled continuations for the trained output head

Rational outputs are printed as numerator/denominator pairs.

The runtime trainer in `main.ml` intentionally keeps the transformer body fixed.
It uses extracted hidden states from the Rocq model, optimizes only the output
projection in the OCaml driver, and then converts the trained head back into
small rational weights for extracted prediction and generation.

The Rocq development now contains two training surfaces:

- a proved output-head training path with reverse-mode gradients and SGD
- a whole-model training path that backpropagates through embeddings, attention,
  the MLP, and the output projection, then drives SGD and Adam-style updates

The executable now prints both a formal output-head demo and a formal whole-model
demo before the OCaml-side runtime trainer. The runtime trainer remains the
lighter frozen-body path, while the extracted whole-model demo gives the build
and CI path a concrete exercised surface for the heavier optimizer definitions.
For runtime experiments, `main.ml` can also load a small whitespace-tokenized
corpus from a text file by passing a path on the command line or by setting
`MICROGPT_CORPUS`. The repository includes `data/demo_corpus.txt`, and CI runs
the executable against that file rather than the built-in fallback.

## Build

Build from a native Linux tree with Rocq/Coq 9.0 and OCaml 4.14:

```bash
coqc MicroGPT.v
ocamlopt -c microgpt_extracted.mli
ocamlopt -c microgpt_extracted.ml
ocamlopt -c main.ml
ocamlopt microgpt_extracted.cmx main.cmx -o microgpt_demo
./microgpt_demo
```

## CI

GitHub Actions runs the same pipeline on every push and pull request:

1. install Rocq/Coq 9.0.0
2. prove `MicroGPT.v`
3. generate `microgpt_extracted.ml` and `microgpt_extracted.mli`
4. build the OCaml executable
5. run the executable and assert that the formal and runtime demo sections appear

## Next

Natural follow-on work includes:

- strengthening proofs around the whole-model gradient and optimizer path
- replacing the current squared-loss training objective with a richer token objective
- introducing a more realistic floating-point or fixed-point numeric model inside the theorem-bearing core
- scaling the vocabulary and corpus surfaces past the built-in toy setting
- proving stronger equivalences between optimized and reference implementations
- targeting additional extracted runtimes, including Crane
