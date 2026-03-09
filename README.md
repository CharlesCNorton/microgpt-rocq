# microgpt-rocq

`microgpt-rocq` is a monolithic Rocq formalization of a small transformer-style language-model core together with OCaml extraction.

The current repository contains:

- a single Rocq development in `MicroGPT.v`
- a small OCaml driver in `main.ml`
- extracted OCaml artifacts generated from the Rocq source

## Scope

The implemented model is inference-only and intentionally proof-friendly. It includes:

- token embeddings
- query/key/value projections
- causal self-attention
- an MLP block
- output logits
- next-token prediction by argmax

Scalars are exact integers (`Z`). Attention uses the positive kernel:

`1 + |dot(q, k)|`

instead of exponential softmax. This keeps the program total and makes the core properties easier to prove while preserving a transformer-shaped forward pass.

## Proven Properties

`MicroGPT.v` proves:

- vector and matrix shape preservation
- attention output shape preservation
- causal prefix invariance for attention
- transformer block shape preservation
- forward-pass output shape preservation
- demo output length and vocabulary bounds
- the concrete demo prediction equality `demo_prediction = 3`

Invalid token lookups fall back to the zero vector, so the extracted program remains total.

## Build

Build from the native Linux tree:

```bash
coqc MicroGPT.v
ocamlopt -c microgpt_extracted.mli
ocamlopt -c microgpt_extracted.ml
ocamlopt -c main.ml
ocamlopt microgpt_extracted.cmx main.cmx -o microgpt_demo
./microgpt_demo
```

## Demo Output

```text
tokens=[0; 2; 1]
prediction=3
logits=[[3; 0; 3; 6]; [6; 4; 10; 16]; [3; 5; 8; 11]]
```

## Next

Natural follow-on work includes:

- replacing the current attention kernel with a richer normalization scheme
- adding a trainable loss and reverse-mode differentiation
- moving from exact integers to a more realistic numeric model
- proving equivalence between alternate implementations of the forward pass
- targeting additional extracted runtimes, including Crane
