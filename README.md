# microgpt-rocq

`microgpt-rocq` is a monolithic Rocq formalization of a small transformer-style language-model core with OCaml extraction.

The repository contains:

- a single theorem-bearing Rocq development in `MicroGPT.v`
- a small OCaml driver in `main.ml`
- extracted OCaml artifacts generated from the Rocq source
- a GitHub Actions workflow that proves, extracts, builds, and runs the executable

## What Is Implemented

The current model is a compact transformer-style language-model core with attached verified training and generation surfaces.

Implemented pieces:

- token embeddings
- query/key/value projections
- causal self-attention
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
- a frozen-body output-head training loop in the OCaml executable
- deterministic and sampled generation paths in the OCaml executable

Scalars are exact rationals (`Q`), not integers. Attention uses the positive kernel

`1 + dot(q, k)^2`

followed by explicit normalization by the prefix score sum. This keeps the attention step exact while making it materially closer to a true normalized weighting scheme than the earlier unnormalized integer baseline.

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
- a runtime training demo over a tiny token corpus
- a before/after loss trace for a cold output head trained against extracted hidden states
- before/after greedy continuations for the trained output head
- before/after sampled continuations for the trained output head

Rational outputs are printed as numerator/denominator pairs.

The runtime trainer in `main.ml` intentionally keeps the transformer body fixed.
It uses extracted hidden states from the Rocq model, optimizes only the output
projection in the OCaml driver, and then converts the trained head back into
small rational weights for extracted prediction and generation.

The Rocq development now also contains a fully formalized output-head training
surface. That formal path covers per-example logits loss, batch gradients,
SGD updates, repeated output-head training steps, and model-shape preservation
through those updates.

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
5. run the executable

## Next

Natural follow-on work includes:

- extending reverse-mode differentiation from the readout head to the transformer core
- replacing the current squared-loss output-head trainer with a proved end-to-end token-training objective for the full transformer
- introducing a more realistic floating-point or fixed-point numeric model inside the theorem-bearing core
- proving stronger equivalences between optimized and reference implementations
- moving the remaining executable-side optimizer and data workflow into the proved Rocq development
- targeting additional extracted runtimes, including Crane
