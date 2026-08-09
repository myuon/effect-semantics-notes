# Lean API documentation build

This nested Lake project follows the upstream `doc-gen4` layout and shares the
parent project's package cache.

```sh
cd formal/docbuild
DOCGEN_SRC=github DISABLE_EQUATIONS=1 lake build EffectSemantics:docs
```

The generated site is written to `.lake/build/doc`.  GitHub Pages copies that
directory to `/lean/` after building the MyST research notes.
