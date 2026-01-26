
From Stdlib Require Import String ZArith Reals List.
Import ListNotations.

Open Scope string_scope.


(* N^+ : positive naturals *)
Definition Npos := positive.



(* =============================================================== *)
(* =======                  Object Models                  ======= *)
(* =============================================================== *)



Definition class_name := string.
Definition attr_name  := string.
Definition assoc_name := string.
Definition role_name := string.
Definition mult_set := list Npos.


Inductive T_b : Type :=
  | Tb_Integer | Tb_Real | Tb_Boolean | Tb_String.

(* Inductive T_c : Type :=
  | Tc_Object : class_name -> T_c. *)


(* 一个属性声明：a : t *)
Record attr_decl : Type := {
  a : attr_name;
  t : T_b
}.



Record obj_model : Type := {
  (* a set of classes *)
  CLASS : list class_name;

  (* a set of attributes for each class *)
  ATT   : class_name -> list attr_decl;

  (* a set of associations *)
  ASSOC : list assoc_name;

  (* associates(as) = <c1,c2>  (binary associations) *)
  associates : assoc_name -> (class_name * class_name);

  (* roles(as) = <r1,r2> *)
  roles : assoc_name -> (role_name * role_name);

  (* multiplicities(as) = <M1,M2> *)
  multiplicities : assoc_name -> (mult_set * mult_set)

}.


Inductive T_c (M : obj_model) : class_name -> Type :=
  | Tc_Object : forall c, In c (CLASS M) -> T_c M c.


Inductive T_hat (M : obj_model) : Type :=
  | TyBasic  : T_b -> T_hat M
  | TyObject : forall c, T_c M c -> T_hat M.



Inductive T_expr (M : obj_model) : Type :=
  | TyNonColl : T_hat M -> T_expr M
  | TyBag     : T_hat M -> T_expr M.



(* Well-formedness conditions *)



Definition mem_str (x : string) (xs : list string) : bool :=
  existsb (String.eqb x) xs.

Fixpoint union_nodup (xs ys : list string) : list string :=
  match xs with
  | [] => ys
  | x :: xs' =>
      if mem_str x ys then union_nodup xs' ys
      else union_nodup xs' (x :: ys)
  end.


Definition participates (M : obj_model) (c : class_name) (asso : assoc_name) : bool :=
  let (c1, c2) := associates M asso in
  (String.eqb c c1) || (String.eqb c c2).

Definition participating (M : obj_model) (c : class_name) : list assoc_name :=
  filter (participates M c) (ASSOC M).



Definition navends_pair (M : obj_model) (c : class_name) (asso : assoc_name)
  : list role_name :=
  let (c1, c2) := associates M asso in
  let (r1, r2) := roles M asso in
  if String.eqb c c1 then [r2]
  else if String.eqb c c2 then [r1]
  else [].


Fixpoint navends_all_aux (M : obj_model) (c : class_name) (assocs : list assoc_name)
  : list role_name :=
  match assocs with
  | [] => []
  | asso :: assocs' =>
      union_nodup (navends_pair M c asso) (navends_all_aux M c assocs')
  end.

Definition navends (M : obj_model) (c : class_name) : list role_name :=
  navends_all_aux M c (participating M c).




Definition wf_CLASS (M : obj_model) : Prop :=
  NoDup (CLASS M).



Definition wf_ATT_type_unique (M : obj_model) : Prop :=
  forall c,
    In c (CLASS M) ->
    forall ad1 ad2,
      In ad1 (ATT M c) ->
      In ad2 (ATT M c) ->
      a ad1 = a ad2 ->
      t ad1 = t ad2.


Definition wf_ASSOC (M : obj_model) : Prop :=
  NoDup (ASSOC M).

  

Definition wf_ROLES (M : obj_model) : Prop :=
  forall asso,
    In asso (ASSOC M) ->
    let (r1, r2) := roles M asso in
    r1 <> r2.




Definition wf_Multiplicities (M : obj_model) : Prop :=
  forall asso,
    In asso (ASSOC M) ->
    let (M1, M2) := multiplicities M asso in
    M1 <> [] /\
    M2 <> [] /\
    NoDup M1 /\
    NoDup M2.



  
Definition wf_ATT_NAVENDS_distinct (M : obj_model) : Prop :=
  forall c ad r,
    In c (CLASS M) ->
    In ad (ATT M c) ->
    In r (navends M c) ->
    a ad <> r.





Definition wf_obj_model (M : obj_model) : Prop :=
  wf_CLASS M /\
  wf_ATT_type_unique M /\
  wf_ASSOC M /\
  wf_ROLES M /\
  wf_Multiplicities M /\
  wf_ATT_NAVENDS_distinct M.









(* =============================================================== *)
(* =======                  operations                     ======= *)
(* =============================================================== *)







Inductive basic_sym : Type :=
    (* Unary and binary arithmetic operations *)
    | UNeg | UAbs | UFloor | URound
    | BAdd | BSub | BMul | BDiv | BMax | BMin | BIntdiv | BIntMod

    (* Comparison operations *)
    | BLt | BLe | BGt | BGe | BEq | BNe

    (* Boolean operations *)
    | UNot | BAnd | BOr | BXor | BImplies

    (* String operations *)
    | USize | UToUpper | UToLower | BConcat | Substring

    (* no parameter operations *)
    | KInt  : Z -> basic_sym
    | KReal : R -> basic_sym
    | KBool : bool -> basic_sym
    | KStr  : string -> basic_sym.


Inductive obj_sym : Type :=
    | CAllInstances : class_name -> obj_sym
    | CAttr         : class_name -> attr_name -> obj_sym
    | CNav1         : class_name -> role_name -> obj_sym
    | CNavSet       : class_name -> role_name -> obj_sym.



Inductive col_sym : Type :=

    (* Constructors *)
    (* | MKSet  *)
    | MKBag

    (* Collection Operations *)
    | ColSize | ColCount | ColIncludes | ColExcludes | ColIncludesAll | ColExcludesAll
    | ColIsEmpty | ColNotEmpty | ColSum 

    (* Bag Operations *)
    | ColUnion | ColIntersection | ColDifference | ColSymDifference .





Inductive op_symbols : Type := (* ω *)
    | SymBasic : basic_sym -> op_symbols
    | SymObj   : obj_sym   -> op_symbols
    | SymCol   : col_sym   -> op_symbols.





Definition tb (M : obj_model) (b : T_b) : T_expr M := TyNonColl M (TyBasic M b).
Definition th (M : obj_model) (t : T_hat M) : T_expr M := TyNonColl M t.



Definition const_ty (s : basic_sym) : option T_b :=
  match s with
  | KInt  _ => Some Tb_Integer
  | KReal _ => Some Tb_Real
  | KBool _ => Some Tb_Boolean
  | KStr  _ => Some Tb_String
  | _ => None
  end.





(* ===========================   Basic operations ================ *)




Inductive Omega_B (M : obj_model) : op_symbols -> list (T_expr M)  -> T_expr M -> Prop :=

    (*  constants: k : -> t  *)
    | OB_Const :
        forall k b,
          const_ty k = Some b ->
          Omega_B M
            (SymBasic k)
            []
            (tb M b)

    (*  Integer × Integer -> Integer  *)
    | OB_IntInt_Int :
        forall o,
          In o [BAdd; BSub; BMul; BMax; BMin; BIntdiv; BIntMod] ->
          Omega_B M
            (SymBasic o)
            [tb M Tb_Integer; tb M Tb_Integer]
            (tb M Tb_Integer)


    (*  Real × t -> Real  *)
    | OB_RealLeft :
        forall o t,
          In o [BAdd; BSub; BMul; BMax; BMin] ->
          In t [Tb_Integer; Tb_Real] ->
          Omega_B M
            (SymBasic o)
            [tb M Tb_Real; tb M t]
            (tb M Tb_Real)


    (*  t × Real -> Real  *)
    | OB_RealRight :
        forall o t,
          In o [BAdd; BSub; BMul; BMax; BMin] ->
          In t [Tb_Integer; Tb_Real] ->
          Omega_B M
            (SymBasic o)
            [tb M t; tb M Tb_Real]
            (tb M Tb_Real)

    (*  division: t1 × t2 -> Real  *)
    | OB_DivReal :
        forall t1 t2,
          In t1 [Tb_Integer; Tb_Real] ->
          In t2 [Tb_Integer; Tb_Real] ->
          Omega_B M
            (SymBasic BDiv)
            [tb M t1; tb M t2]
            (tb M Tb_Real)

    (*  unary numeric ops: t -> t  *)
    | OB_UnaryNum :
        forall o t,
          In o [UNeg; UAbs] ->
          In t [Tb_Integer; Tb_Real] ->
          Omega_B M
            (SymBasic o)
            [tb M t]
            (tb M t)

    (*  floor, round: t -> Integer  *)
    | OB_ToInt :
        forall o t,
          In o [UFloor; URound] ->
          In t [Tb_Integer; Tb_Real] ->
          Omega_B M
            (SymBasic o)
            [tb M t]
            (tb M Tb_Integer)



    (*  comparisons: t × t -> Boolean  *)
    | OB_Compare :
        forall o t,
          In o [BLt; BLe; BGt; BGe] ->
          In t [Tb_Integer; Tb_Real; Tb_String] ->
          Omega_B M
            (SymBasic o)
            [tb M t; tb M t]
            (tb M Tb_Boolean)


    (*  Boolean binary ops  *)
    | OB_BoolBin :
        forall o,
          In o [BAnd; BOr; BXor; BImplies] ->
          Omega_B M
            (SymBasic o)
            [tb M Tb_Boolean; tb M Tb_Boolean]
            (tb M Tb_Boolean)

    (*  not  *)
    | OB_Not :
          Omega_B M
            (SymBasic UNot)
            [tb M Tb_Boolean]
            (tb M Tb_Boolean)

    (*  size  *)
    | OB_Size :
          Omega_B M
            (SymBasic USize)
            [tb M Tb_String]
            (tb M Tb_Integer)

    (*  concat  *)
    | OB_Concat :
          Omega_B M
            (SymBasic BConcat)
            [tb M Tb_String; tb M Tb_String]
            (tb M Tb_String)


    (*  string unary  *)
    | OB_StringUnary :
        forall o,
          In o [UToUpper; UToLower] ->
          Omega_B M
            (SymBasic o)
            [tb M Tb_String]
            (tb M Tb_String)

    (*  substring  *)
    | OB_Substring :
          Omega_B M
            (SymBasic Substring)
            [tb M Tb_String; tb M Tb_Integer; tb M Tb_Integer]
            (tb M Tb_String)

    (*  Common operations  *)

    | OC_Eq :
        forall (t : T_hat M),
          Omega_B M
            (SymBasic BEq)
            [th M t; th M t]
            (tb M Tb_Boolean)
    | OC_Ne :
        forall (t : T_hat M),
          Omega_B M
            (SymBasic BNe)
            [th M t; th M t]
            (tb M Tb_Boolean).





(* ======================   Object operations ======================= *)




(* Definition typeOf (M : obj_model) (c : class_name) : T_c M c := Tc_Object M c. *)

Definition typeOf (M : obj_model) (c : class_name) (H : In c (CLASS M)) : T_c M c :=
  Tc_Object M c H.

(* Definition classOf (t : T_c M) : class_name :=
  match t with
  | Tc_Object c => c
  end. *)

Definition classOf (M : obj_model) (c : class_name) (_ : T_c M c) : class_name := c.




Definition mult_only_one (Mj : mult_set) : Prop :=
  forall p, In p Mj -> p = 1%positive. 

Definition mult_not_only_one (Mj : mult_set) : Prop :=
  exists p, In p Mj /\ p <> 1%positive.


Definition nav_role_mult (M : obj_model) (c : class_name) (asso : assoc_name)
  (rj : role_name) (Mj : mult_set) : Prop :=
  let (c1, c2) := associates M asso in
  let (r1, r2) := roles M asso in
  let (M1, M2) := multiplicities M asso in
  (c = c1 /\ rj = r2 /\ Mj = M2) \/
  (c = c2 /\ rj = r1 /\ Mj = M1).


Definition other_class
  (M : obj_model)
  (c : class_name)
  (asso : assoc_name)
  : class_name :=
  let (c1, c2) := associates M asso in
  if String.eqb c c1 then c2 else c1.


Definition other_class_ty
  (M : obj_model)
  (c : class_name)
  (asso : assoc_name)
  (Hother : In (other_class M c asso) (CLASS M))
  : T_hat M :=
  TyObject M (other_class M c asso)
    (typeOf M (other_class M c asso) Hother).




Definition tc (M : obj_model) (c : class_name) (H : In c (CLASS M)) : T_hat M :=
  TyObject M c (typeOf M c H).



Inductive Omega_C (M : obj_model) : op_symbols -> list (T_expr M) -> T_expr M -> Prop :=

    (*  allInstances_{t_c} : -> Set(t_c)  *)
    | OC_AllInstances :
        forall c (Hc : In c (CLASS M)),
          Omega_C M
            (SymObj (CAllInstances c))
            []
            (TyBag M (tc M c Hc))


    (*  attribute: a : t_c -> t   *)
    | OC_Attr :
        forall c (ad : attr_decl)
              (Hc : In c (CLASS M)),
          In ad (ATT M c) ->
          Omega_C M
            (SymObj (CAttr c (a ad)))
            [th M (tc M c Hc)]
            (tb M (t ad))

        
    (*  navigation, multiplicity = {1} : t_c -> t_cj  *)
    | OC_Nav1 :
        forall c asso rj Mj
              (Hc : In c (CLASS M))
              (Hother : In (other_class M c asso) (CLASS M)),
          In asso (participating M c) ->
          nav_role_mult M c asso rj Mj ->
          mult_only_one Mj ->
          Omega_C M
            (SymObj (CNav1 c rj))
            [th M (tc M c Hc)]
            (th M (other_class_ty M c asso Hother))


    (* navigation, multiplicity != {1} : t_c -> Set(t_cj) *)
    | OC_NavSet :
        forall c asso rj Mj
              (Hc : In c (CLASS M))
              (Hother : In (other_class M c asso) (CLASS M)),
          In asso (participating M c) ->
          nav_role_mult M c asso rj Mj ->
          mult_not_only_one Mj ->
          Omega_C M
            (SymObj (CNavSet c rj))
            [th M (tc M c Hc)]
            (TyBag M (other_class_ty M c asso Hother)).




(* ======================   Collection  operations ======================= *)



(* 参数列表全是某个类型 t *)
Definition all_of (M : obj_model) (t : T_expr M) (ps : list (T_expr M)) : Prop :=
  Forall (fun x => x = t) ps.


Definition nc (M : obj_model) (t : T_hat M) : T_expr M :=
  TyNonColl M t.


Inductive Omega_Expr (M : obj_model) : op_symbols -> list (T_expr M) -> (T_expr M) -> Prop :=



| OE_MKBag :
    forall (t : T_hat M) (ps : list (T_expr M)),
      all_of M (nc M t) ps ->
      Omega_Expr M
        (SymCol MKBag)
        ps
        (TyBag M t)


    | OE_ColSize :
        forall t,
          Omega_Expr M
            (SymCol ColSize)
            [TyBag M t]
            (tb  M Tb_Integer)




    | OE_ColCount :
        forall t,
          Omega_Expr M
            (SymCol ColCount)
            [TyBag  M t; nc  M t]
            (tb  M Tb_Integer)


    | OE_ColIncludes :
        forall t,
          Omega_Expr M
            (SymCol ColIncludes)
            [TyBag M t; nc M t]
            (tb M Tb_Boolean)

    | OE_ColExcludes :
        forall t,
          Omega_Expr M
            (SymCol ColExcludes)
            [TyBag M t; nc M t]
            (tb M Tb_Boolean)

    | OE_ColIncludesAll :
        forall t,
          Omega_Expr M
            (SymCol ColIncludesAll)
            [TyBag M t; TyBag M t]
            (tb M Tb_Boolean)

    | OE_ColExcludesAll :
        forall t,
          Omega_Expr M
            (SymCol ColExcludesAll)
            [TyBag M t; TyBag M t]
            (tb M Tb_Boolean)


    | OE_ColIsEmpty :
        forall t,
          Omega_Expr M
            (SymCol ColIsEmpty)
            [TyBag M t]
            (tb M Tb_Boolean)

    | OE_ColNotEmpty :
        forall t,
          Omega_Expr M
            (SymCol ColNotEmpty)
            [TyBag M t]
            (tb M Tb_Boolean)


    | OE_ColSum :
        forall t,
          In t [TyBasic M Tb_Integer; TyBasic M Tb_Real] ->
          Omega_Expr M
            (SymCol ColSum)
            [TyBag M t]
            (nc M t)

    | OE_Union :
        forall t,
          Omega_Expr M
            (SymCol ColUnion)
            [TyBag M t; TyBag M t]
            (TyBag M t)


    | OE_Intersection :
        forall t,
          Omega_Expr M
            (SymCol ColIntersection)
            [TyBag M t; TyBag M t]
            (TyBag M t)


    | OE_Difference :
        forall t,
          Omega_Expr M
            (SymCol ColDifference)
            [TyBag M t; TyBag M t]
            (TyBag M t)


    | OE_SymDifference :
        forall t,
          Omega_Expr M
            (SymCol ColSymDifference)
            [TyBag M t; TyBag M t]
            (TyBag M t)
    .


(* ======================   Data Signature ======================= *)




Inductive Omega_all (M : obj_model)
  : op_symbols -> list (T_expr M) -> (T_expr M) -> Prop :=
    | OM_B :
        forall s ps r,
          Omega_B M s ps r ->
          Omega_all M s ps r
    | OM_C :
        forall s ps r,
          Omega_C M s ps r ->
          Omega_all M s ps r
    | OM_Expr :
        forall s ps r,
          Omega_Expr M s ps r ->
          Omega_all M s ps r.





Record data_signature (M : obj_model) : Type := {
  T_M  : Type := T_expr M;
  Omega_M : op_symbols -> list (T_M) -> T_M -> Prop := Omega_all M
}.



(* ------------------------------------------------------------ *)
(* Expressions over a signature Σ_M and a family Var            *)
(* ------------------------------------------------------------ *)


Definition var_name := string.

Definition Var_of (M : obj_model)  : Type :=
  T_expr M -> list var_name.

Definition InVar_of (M : obj_model)
  (V : Var_of M) (t : T_expr M) (x : var_name) : Prop :=
  In x (V t).



Inductive Expr (M : obj_model) (V : Var_of M)
      : T_expr M -> Type :=
          (* A.29(i): v ∈ Var_t ⇒ v ∈ Expr_t *)
    | EVar :
        forall (t : T_expr M) (x : var_name),
          InVar_of M V t x ->
          Expr M V t

    (* A.29(iii)(a)(b): ω : ps -> r ∈ Ω_M, 且 args ∈ Exprs ps *)
    | EOp  :
        forall (s : op_symbols) (ps : list (T_expr M)) (r : T_expr M),
          Omega_all M s ps r ->
          Exprs M V ps ->
          Expr M V r
    (* iterate: e1 : Bag t1, v1 : t1, v2 : t2, e2 : t2, e3 : t2  ->  t2 *)
    | EIterate :
        forall (t1 : T_hat M )
              (t2 : T_expr M)
              (e1 : Expr M V (TyBag M t1))
              (v1 v2 : var_name)
              (e2 e3 : Expr M V t2),
          InVar_of M V (TyNonColl M t1) v1 ->   (* v1 : t1 的类型应当是 T_expr M *)
          InVar_of M V t2 v2 ->
          Expr M V t2


    with Exprs (M : obj_model) (V : Var_of M)
      : list (T_expr M) -> Type :=
        | ENil  : Exprs M V []
        | ECons : forall (t : T_expr M) (ts : list (T_expr M)),
            Expr M V t ->
            Exprs M V ts ->
            Exprs M V (t :: ts).




Definition mem_var (x : var_name) (xs : list var_name) : bool :=
  existsb (String.eqb x) xs.



Fixpoint remove_all (x : var_name) (xs : list var_name) : list var_name :=
  match xs with
  | [] => []
  | y :: ys =>
      if String.eqb x y then remove_all x ys else y :: remove_all x ys
  end.

Definition remove2 (x y : var_name) (xs : list var_name) : list var_name :=
  remove_all y (remove_all x xs).



Fixpoint free (M : obj_model) (V : Var_of M)
  (t : T_expr M) (e : Expr M V t) : list var_name :=
    match e with
    | EVar _ _ _ x _ =>
        [x]

    | EOp _ _ _ ps r _ args =>
        (* ω(args)：自由变量 = 参数自由变量并集；ps=[] 时 args=ENil -> [] *)
        free_args M V ps args

    | EIterate _ _ t1 t2 e1 v1 v2 e2 e3 _ _ =>
        remove2 v1 v2
          (union_nodup (free M V (TyBag M t1) e1)
            (union_nodup (free M V t2 e2)
                        (free M V t2 e3)))
    end
    
    with free_args (M : obj_model) (V : Var_of M)
      (ps : list (T_expr M)) (es : Exprs M V ps) : list var_name :=
      match es with
      | ENil _ _ =>
          []
      | ECons _ _ t ts e es' =>
          union_nodup (free M V t e) (free_args M V ts es')
      end.



