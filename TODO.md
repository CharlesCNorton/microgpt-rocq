# TODO

Remaining work, in logical order:

1. Replace the current attention kernel with standard softmax attention.
2. Add a norm layer to the transformer block and carry its invariants through the forward and training surfaces.
3. Add multi-head attention and prove head splitting, recombination, and output shapes stay well-formed.
4. Give each layer its own parameters instead of using shared-weight depth.
5. Move practical full-model training onto the extracted path so there is one execution lane instead of a split between extracted demos and native OCaml training.
6. Add a finite-precision and error model for the practical training path.
7. Expand the tokenizer and corpus pipeline beyond the small demo setup in `main.ml`.
