From Stdlib Require Import String ZArith Reals.

Definition Rfloor_real (r : R) (z : Z) : Prop :=
  (IZR z <= r < IZR (z + 1))%R.



Definition Rround_real (r : R) (z : Z) : Prop :=
Rfloor_real (r + /2) z.