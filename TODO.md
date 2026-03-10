# TODO

Remaining work, in logical order:

1. Add a norm layer to the transformer block and carry its invariants through the forward and training surfaces.
2. Add multi-head attention and prove head splitting, recombination, and output shapes stay well-formed.
3. Give each layer its own parameters instead of using shared-weight depth.
4. Move practical full-model training onto the extracted path so there is one execution lane instead of a split between extracted demos and native OCaml training.
5. Add a finite-precision and error model for the practical training path.
6. Expand the tokenizer and corpus pipeline beyond the small demo setup in `main.ml`.
