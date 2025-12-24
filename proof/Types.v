From Stdlib Require Import String.



(* ================================= Type ======================================= *)

Inductive ty : Type :=
| Ty_Bool : ty
| Ty_Int : ty
| Ty_Real : ty
| Ty_String : ty
| Ty_Bag : ty -> ty
| Ty_Object: string -> ty.



    