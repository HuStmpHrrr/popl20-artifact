## Undecidability of D<: and Its Decidable Fragments

The binary dependencies are

* Coq 8.8.2
* Agda 2.5.4.2

Library dependencies are in `lib/` folder, which will be built automatically.

For a recommended way to installing Coq and Agda, please refer to the end of this
page.

Dependencies are automatically built by

``` shell
make -B
```

This command will also build `dsub/` folder which contains the Coq proofs.

`fsub/` folder can be built by 

``` shell
make fsub
```

The Agda proofs can be verified by

``` shell
cd agda/
agda-2.5.4.2 Everything.agda
```
or by loading from Emacs.

## Correspondence Between The Paper and Formalization

The formalization is done with a combination of Agda and Coq. The undecidability
proofs are done in Agda (section 4) and the proofs of algorimic subtyping are done in
Coq (section 5 and 6).

The formalization is axiom-free, predicative and purely constructive. 

### Folder structure

The artifact consists of the following folders.

* [`agda/`](agda/Everything.html) contains the undecidability proofs in Agda.
* [`fsub/`](fsub/toc.html) contains the proofs of algorithmic subtyping of `F<:` in Coq.
* [`dsub/`](dsub/toc.html) contains the proofs of algorithmic subtyping of `D<:` in Coq.
* `lib/` contains external dependencies.
* `share/` contains library specifically designed for this project.


### Structure of Agda Proofs

The entry point is [Everything.agda](agda/Everything.html). The structure of the files
are explained there.

### Structure of Coq Proofs

There are Coq proofs in [`fsub/`](fsub/toc.html) and [`dsub/`](dsub/toc.html), and the
proofs are organized in the following ways:

* `Definition.v` defines the abstract syntax and judgments of the calculus.
* `OperationProperties.v`, `StructuralProperties.v` and `Misc.v` include necessary
  technical setup.
*  `OpeSub.v` defines `OPE<:` and verifies its properties.
* `StrongKernel.v` defines and verifies the properties of strong kernel.

In `dsub/`, there are following additional files:

* `Kernel.v` defines kernel D<: and examines its properties.
* `Step.v` defines step subtyping and examines its properties.
* `Stareat.v` defines stare-at subtyping and examines its properties.

### The undecidability proofs

The paper made brief discussion on why `F<:-` is undecidable. In the Agda proof, this
is justified by reducing from `F<:` deterministic, `F<:d`, to `F<:-`. `F<:d` is an
intermediate calculus in Pierce92, which was shown reducible from TCM, and therefore
`F<:d` is undecidable as well as `F<:-`. 

| Theorem | File                                                | Related Formalization                                                                                     |
|---------|-----------------------------------------------------|-----------------------------------------------------------------------------------------------------------|
| 2       | [DsubFull.agda](agda/DsubFull.html)                 | [`<:⇒<:′`](agda/DsubFull.html#2133) and [`<:′⇒<:`](agda/DsubFull.html#2958)                               |
| 5       | [FsubMinus.agda](agda/FsubMinus.html)               | [`minus⇒deterministic`](agda/FsubMinus.html#29141) and [`deterministic⇒minus`](agda/FsubMinus.html#29388) |
| 6       | [DsubDef.agda](agda/DsubDef.html)                   | [`contraInvertible`](agda/DsubDef.html#8769)                                                              |
|         | [DsubReduced.agda](agda/DsubReduced.html)           | [`⟪⟫-contraEnv`](agda/DsubReduced.html#4239)                                                              |
| 7, 8, 9 | [DsubDef.agda](agda/DsubDef.html)                   | under [`module InvertibleProperties`](agda/DsubDef.html#9405)                                             |
| 10      | [DsubEquivSimpler.agda](agda/DsubEquivSimpler.html) | under [`module SimplerTransitivity`](agda/DsubEquivSimpler.html#3706)                                     |
| 11      | [DsubEquivSimpler.agda](agda/DsubEquivSimpler.html) | [`<:⇒<:″`](agda/DsubEquivSimpler.html#14605) and [`<:″⇒<:`](agda/DsubEquivSimpler.html#15057)             |
| 12, 13  | [DsubEquivSimpler.agda](agda/DsubEquivSimpler.html) | [`F<:⇒D<:`](agda/DsubEquivSimpler.html#18497) and [`D<:⇒F<:`](agda/DsubEquivSimpler.html#18589)           |
| 14      | [DsubNoTrans.agda](agda/DsubNoTrans.html)           | [`F<:⇒D<:`](agda/DsubNoTrans.html#7080) and [`D<:⇒F<:`](agda/DsubNoTrans.html#7174)                       |
| 15, 16  | [DsubTermUndec.agda](agda/DsubTermUndec.html)       | [`F<:⇒typing′`](agda/DsubTermUndec.html#897) and [`typing⇒F<:′`](agda/DsubTermUndec.html#1471)            |

### Kernel D<: and Step subtyping

| Theorem | File                         | Related Formalization                                                                                                                                                                                                                                                      |
|---------|------------------------------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 17      | [Kernel.v](dsub/Kernel.html) | [`subtykn_sound`](dsub/Kernel.html#subtykn_sound)                                                                                                                                                                                                                          |
| 18      | [Step.v](dsub/Step.html)     | [`stp_subty_sound`](dsub/Step.html#stp_subty_sound)                                                                                                                                                                                                                        |
| 19      | [Step.v](dsub/Step.html)     | [`stp_subty_terminates`](dsub/Step.html#stp_subty_terminates)                                                                                                                                                                                                              |
| 20      | [Kernel.v](dsub/Kernel.html) | [`subtykn_refl`](dsub/Kernel.html#subtykn_refl)                                                                                                                                                                                                                            |
| 21      | [Kernel.v](dsub/Kernel.html) | [`trans_on_top`](dsub/Kernel.html#trans_on_top)                                                                                                                                                                                                                            |
| 22      | [Kernel.v](dsub/Kernel.html) | [`trans_on_bot`](dsub/Kernel.html#trans_on_bot)                                                                                                                                                                                                                            |
| 23      | [Kernel.v](dsub/Kernel.html) | [`exposure'_to_subtykn`](dsub/Kernel.html#exposure'_to_subtykn)                                                                                                                                                                                                            |
|         | [Step.v](dsub/Step.html)     | [`exposure_to_exposure'`](dsub/Step.html#exposure_to_exposure'), [`exposure'_to_exposure`](dsub/Step.html#exposure'_to_exposure)                                                                                                                                           |
| 24      | [Kernel.v](dsub/Kernel.html) | [`stp_subty_to_subtykn`](dsub/Kernel.html#stp_subty_to_subtykn)                                                                                                                                                                                                            |
| 25      | [Kernel.v](dsub/Kernel.html) | [`subtykn_to_stp_subty`](dsub/Kernel.html#subtykn_to_stp_subty), [`subtykn_to_stp_subty'`](dsub/Kernel.html#subtykn_to_stp_subty'), [`stp_subty'_to_stp_subty`](dsub/Kernel.html#stp_subty'_to_stp_subty), [`subtykn'_conversions`](dsub/Kernel.html#subtykn'_conversions) |
|         | [Step.v](dsub/Step.html)     | [`exposure_strengthening`](dsub/Step.html#exposure_strengthening)                                                                                                                                                                                                        |

### Strong Kernel D<: and Stare-at subtyping

| Theorem | File                                     | Related Formalization                                                                                                                                                                                                                                                              |
|---------|------------------------------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 26      | [StrongKernel.v](dsub/StrongKernel.html) | [`subtysk_refl`](dsub/StrongKernel.html#subtysk_refl)                                                                                                                                                                                                                              |
| 27      | [StrongKernel.v](dsub/StrongKernel.html) | [`subtykn_to_subtysk`](dsub/StrongKernel.html#subtykn_to_subtysk)                                                                                                                                                                                                                  |
| 28, 32  | [StrongKernel.v](dsub/StrongKernel.html) | [`subtysk_sound`](dsub/StrongKernel.html#subtysk_sound)                                                                                                                                                                                                                            |
| 29      | [OpeSub.v](dsub/OpeSub.html)             | [`ope_sub_refl`](dsub/OpeSub.html#ope_sub_refl)                                                                                                                                                                                                                                    |
| 30      | [OpeSub.v](dsub/OpeSub.html)             | [`ope_sub_trans`](dsub/OpeSub.html#ope_sub_trans)                                                                                                                                                                                                                                  |
| 31      | [OpeSub.v](dsub/OpeSub.html)             | [`ope_narrow_subty`](dsub/OpeSub.html#ope_narrow_subty)                                                                                                                                                                                                                            |
| 33      | [Step.v](dsub/Step.html)                 | [`revealing_gives_prefix`](dsub/Step.html#revealing_gives_prefix)                                                                                                                                                                                                                  |
| 34, 35  | [Stareat.v](dsub/Stareat.html)           | [`revealing_sound`](dsub/Stareat.html#revealing_sound)                                                                                                                                                                                                                             |
| 36      | [Stareat.v](dsub/Stareat.html)           | [`revealing_preserves_wf`](dsub/Stareat.html#revealing_preserves_wf)                                                                                                                                                                                                               |
| 37      | [Stareat.v](dsub/Stareat.html)           | [`upcast_sound`](dsub/Stareat.html#upcast_sound), [`upcast_preserves_wf`](dsub/Stareat.html#upcast_preserves_wf), [`downcast_sound`](dsub/Stareat.html#downcast_sound), [`downcast_preserves_wf`](dsub/Stareat.html#downcast_preserves_wf)                                         |
|         | [Step.v](dsub/Step.html)                 | [`upcast_gives_prefix`](dsub/Step.html#upcast_gives_prefix), [`downcast_gives_prefix`](dsub/Step.html#downcast_gives_prefix)                                                                                                                                                       |
| 38      | [Stareat.v](dsub/Stareat.html)           | [`ope_sub_stareat_sound`](dsub/Stareat.html#ope_sub_stareat_sound)                                                                                                                                                                                                                 |
| 39      | [Stareat.v](dsub/Stareat.html)           | [`bsubtyp_sound`](dsub/Stareat.html#bsubtyp_sound)                                                                                                                                                                                                                                 |
| 40      | [Stareat.v](dsub/Stareat.html)           | [`revealing_terminates`](dsub/Stareat.html#revealing_terminates)                                                                                                                                                                                                                   |
| 41      | [Stareat.v](dsub/Stareat.html)           | [`revealing_measure`](dsub/Stareat.html#revealing_measure), [`upcast_decreases_measure`](dsub/Stareat.html#upcast_decreases_measure), and [`downcast_decreases_measure`](dsub/Stareat.html#downcast_decreases_measure)                                                             |
| 42      | [Stareat.v](dsub/Stareat.html)           | [`stareat_terminates`](dsub/Stareat.html#stareat_terminates)                                                                                                                                                                                                                       |
| 43      | [StrongKernel.v](dsub/StrongKernel.html) | [`revealing_to_subtysk`](dsub/StrongKernel.html#revealing_to_subtysk), [`exposure'_to_subtysk`](dsub/StrongKernel.html#exposure'_to_subtysk)                                                                                                                                       |
| 44      | [StrongKernel.v](dsub/StrongKernel.html) | [`stareat_to_subtysk`](dsub/StrongKernel.html#stareat_to_subtysk), [`stareat'_to_subtysk`](dsub/StrongKernel.html#stareat'_to_subtysk), [`stareat_to_stareat'`](dsub/StrongKernel.html#stareat_to_stareat')                                                                        |
| 45      | [Step.v](dsub/Step.html)                 | [`stareat_strengthening`](dsub/Step.html#stareat_strengthening)                                                                                                                                                                                                                    |
| 46      | [StrongKernel.v](dsub/StrongKernel.html) | [`subtysk_to_stareat`](dsub/StrongKernel.html#subtysk_to_stareat), [`subtysk_to_stareat'`](dsub/StrongKernel.html#subtysk_to_stareat'), [`stareat'_to_stareat`](dsub/StrongKernel.html#stareat'_to_stareat), [`subtysk'_conversions`](dsub/StrongKernel.html#subtysk'_conversions) |


### Proof engineering

To make formalization work, there are proof engineering details that are not exposed
in the paper. They include:

* In Agda, names are modelled using De Bruijn indices.
* In Coq, names are modelled using cofinite quantification. Therefore, in addition to
  requiring a type being closed w.r.t. the context, well-formedness condition also
  requires that the types are locally closed.
* Some conclusions are results of equivalences of intermediate languages which are not
  mentioned in the paper.
* Step subtyping and Stare-at subtyping are modelled as program traces. In addition to
  every input/output, the relations also rely on a name store, very often represented
  by `L`, which means when a free name is drawn from a supply, the name must not be in
  `L`. This is a realistic treatment when free names are necessary in a program trace.
* There are theorems in the paper which require to count the steps of derivation. In
  this case, separate relations are defined. Each of such relations copies its
  corresponding original relation, and additionally has a step counter, usually
  represented by `n`. Then this relation is shown to be equivalent to the original
  one. That is, if the original relation is `R ⊆ X × Y`, then define `R′ ⊆ X × Y × ℕ`,
  such that
  ```
  (x, y) ∈ R ⇔ ∃ n, (x, y, n) ∈ R′
  ```

## Binary Installation

### Installing Coq

Please ensure that all related binaries can be found in `PATH`. If a binary is not
found, please check your the `PATH` of your shell.

To install Coq, it is recommended to install via opam2, which can be installed via

``` shell
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
```

Then the following script will create a switch with the proper compiler version and
install Coq.

``` shell
opam switch create coq-8.8.2 4.05.0
eval $(opam env)
opam pin add coq 8.8.2
```

### Install Agda

It is recommended to build Agda from source. To do so, one would need to install
`stack`. This can be done via

``` shell
curl -sSL https://get.haskellstack.org/ | sh
```

Then the following script will use `stack` to install Agda in `.local/bin/`.

``` shell
git clone https://github.com/agda/agda
cd agda
git checkout release-2.5.4.2
cp stack-8.4.4.yaml stack.yaml
stack stall # it is going to take a while
cp ~/.local/bin/agda ~/.local/bin/agda-2.5.4.2
cp ~/.local/bin/agda-mode ~/.local/bin/agda-mode-2.5.4.2
```
