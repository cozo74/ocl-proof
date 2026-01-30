

From Stdlib Require Import String ZArith Reals List.
Import ListNotations.

From OCL.equivalence Require Import Models OCLSyntax Utils.


Open Scope string_scope.

(* ================================= Typing ======================================= *)




Inductive vhas_type_b : I_b -> T_b -> Prop :=
    | VHTB_Bool :
        forall b : bool,
        vhas_type_b (Ib_Bool b) Tb_Bool
    | VHTB_Int :
        forall n : Z,
        vhas_type_b (Ib_Int n) Tb_Int
    | VHTB_Real :
        forall r : R,
        vhas_type_b (Ib_Real r) Tb_Real
    | VHTB_String :
        forall s : string,
        vhas_type_b (Ib_String s) Tb_String.





(* ====================== helper: I_h vs T_h ====================== *)




Inductive vhas_type_h : I_h -> T_h -> Prop :=

    | VHTH_Basic :
        forall b tb,
        vhas_type_b b tb ->
        vhas_type_h (Ih_Basic b) (Th_Basic tb)

    | VHTH_Object :
        forall c o,
        vhas_type_h (Ih_Object c o) (Th_Object c).




Inductive vhas_type : I_e -> T_e -> Prop :=

    (* ====================== Single ====================== *)

    | VHT_Single :
        forall vh th,
        vhas_type_h vh th ->
        vhas_type (Ie_Single vh) (Te_Single th)

    (* ====================== Bag ====================== *)

    | VHT_Bag :
        forall th vs,
        (forall v, In v vs -> vhas_type_h v th) ->
        vhas_type (Ie_Bag th vs) (Te_Bag th).







Definition unop_type (op : unop) (t : T_e) : option T_e :=
  match op, t with
  | U_Bool  _, Te_Single (Th_Basic Tb_Bool) => Some (Te_Single (Th_Basic Tb_Bool))

  | U_Arith UNeg,   Te_Single (Th_Basic Tb_Int)  => Some (Te_Single (Th_Basic Tb_Int))
  | U_Arith UAbs,   Te_Single (Th_Basic Tb_Int)  => Some (Te_Single (Th_Basic Tb_Int))

  | U_Arith UNeg,   Te_Single (Th_Basic Tb_Real) => Some (Te_Single (Th_Basic Tb_Real))
  | U_Arith UAbs,   Te_Single (Th_Basic Tb_Real) => Some (Te_Single (Th_Basic Tb_Real))
  | U_Arith UFloor, Te_Single (Th_Basic Tb_Real) => Some (Te_Single (Th_Basic Tb_Int))
  | U_Arith URound, Te_Single (Th_Basic Tb_Real) => Some (Te_Single (Th_Basic Tb_Int))

  | U_Str UToUpper, Te_Single (Th_Basic Tb_String) => Some (Te_Single (Th_Basic Tb_String))
  | U_Str UToLower, Te_Single (Th_Basic Tb_String) => Some (Te_Single (Th_Basic Tb_String))
  | U_Str USize,    Te_Single (Th_Basic Tb_String) => Some (Te_Single (Th_Basic Tb_Int))

  | _, _ => None
  end.








Definition binop_type (op : binop) (t1 t2 : T_e) : option T_e :=
  match op, t1, t2 with
  | B_Bool  _, Te_Single (Th_Basic Tb_Bool), Te_Single (Th_Basic Tb_Bool) => Some (Te_Single (Th_Basic Tb_Bool))

  (* 比较：数值允许 Int/Real 混合，结果 Bool *)
  | B_Comp  _, Te_Single (Th_Basic Tb_Int),  Te_Single (Th_Basic Tb_Int)  => Some (Te_Single (Th_Basic Tb_Bool))
  | B_Comp  _, Te_Single (Th_Basic Tb_Int),  Te_Single (Th_Basic Tb_Real) => Some (Te_Single (Th_Basic Tb_Bool))
  | B_Comp  _, Te_Single (Th_Basic Tb_Real), Te_Single (Th_Basic Tb_Int)  => Some (Te_Single (Th_Basic Tb_Bool))
  | B_Comp  _, Te_Single (Th_Basic Tb_Real), Te_Single (Th_Basic Tb_Real) => Some (Te_Single (Th_Basic Tb_Bool))

  (* String/Object 仅限 Eq/Ne，结果 Bool（按你之前的语义） *)
  | B_Comp  BEq, Te_Single (Th_Basic Tb_String), Te_Single (Th_Basic Tb_String) => Some (Te_Single (Th_Basic Tb_Bool))
  | B_Comp  BNe, Te_Single (Th_Basic Tb_String), Te_Single (Th_Basic Tb_String) => Some (Te_Single (Th_Basic Tb_Bool))

  | B_Comp  BEq, Te_Single (Th_Object _), Te_Single (Th_Object _) => Some (Te_Single (Th_Basic Tb_Bool))
  | B_Comp  BNe, Te_Single (Th_Object _), Te_Single (Th_Object _) => Some (Te_Single (Th_Basic Tb_Bool))

  (* 算术：Int op Int -> Int（但 Div -> Real）；涉及 Real -> Real *)
  | B_Arith BAdd, Te_Single (Th_Basic Tb_Int),  Te_Single (Th_Basic Tb_Int)  => Some (Te_Single (Th_Basic Tb_Int))
  | B_Arith BSub, Te_Single (Th_Basic Tb_Int),  Te_Single (Th_Basic Tb_Int)  => Some (Te_Single (Th_Basic Tb_Int))
  | B_Arith BMul, Te_Single (Th_Basic Tb_Int),  Te_Single (Th_Basic Tb_Int)  => Some (Te_Single (Th_Basic Tb_Int))
  | B_Arith BDiv, Te_Single (Th_Basic Tb_Int),  Te_Single (Th_Basic Tb_Int)  => Some (Te_Single (Th_Basic Tb_Real))

  | B_Arith _,    Te_Single (Th_Basic Tb_Int),  Te_Single (Th_Basic Tb_Real) => Some (Te_Single (Th_Basic Tb_Real))
  | B_Arith _,    Te_Single (Th_Basic Tb_Real), Te_Single (Th_Basic Tb_Int)  => Some (Te_Single (Th_Basic Tb_Real))
  | B_Arith _,    Te_Single (Th_Basic Tb_Real), Te_Single (Th_Basic Tb_Real) => Some (Te_Single (Th_Basic Tb_Real))

  | B_Str   BConcat, Te_Single (Th_Basic Tb_String), Te_Single (Th_Basic Tb_String) => Some (Te_Single (Th_Basic Tb_String))

  (* 聚合二元：max/min Int/Real；mod/divInt Int（按你现有 binop 划分） *)
  | B_Agg BMax,    Te_Single (Th_Basic Tb_Int),  Te_Single (Th_Basic Tb_Int)  => Some (Te_Single (Th_Basic Tb_Int))
  | B_Agg BMin,    Te_Single (Th_Basic Tb_Int),  Te_Single (Th_Basic Tb_Int)  => Some (Te_Single (Th_Basic Tb_Int))
  | B_Agg BMax,    Te_Single (Th_Basic Tb_Real), Te_Single (Th_Basic Tb_Real) => Some (Te_Single (Th_Basic Tb_Real))
  | B_Agg BMin,    Te_Single (Th_Basic Tb_Real), Te_Single (Th_Basic Tb_Real) => Some (Te_Single (Th_Basic Tb_Real))
  | B_Agg BMod,    Te_Single (Th_Basic Tb_Int),  Te_Single (Th_Basic Tb_Int)  => Some (Te_Single (Th_Basic Tb_Int))
  | B_Agg BDivInt, Te_Single (Th_Basic Tb_Int),  Te_Single (Th_Basic Tb_Int)  => Some (Te_Single (Th_Basic Tb_Int))

  | _, _, _ => None
  end.



Definition aggop_type (op : aggop) (src_ty : T_h) : option T_h :=
  match op, src_ty with
  | AggSize, _ => Some (Th_Basic Tb_Int)

  | AggMin, Th_Basic Tb_Int  => Some (Th_Basic Tb_Int)
  | AggMax, Th_Basic Tb_Int  => Some (Th_Basic Tb_Int)
  | AggSum, Th_Basic Tb_Int  => Some (Th_Basic Tb_Int)

  | AggMin, Th_Basic Tb_Real => Some (Th_Basic Tb_Real)
  | AggMax, Th_Basic Tb_Real => Some (Th_Basic Tb_Real)
  | AggSum, Th_Basic Tb_Real => Some (Th_Basic Tb_Real)

  | _, _ => None
  end.









Definition T_b_eqb (t1 t2 : T_b) : bool :=
  match t1, t2 with
  | Tb_Bool,   Tb_Bool
  | Tb_Int,    Tb_Int
  | Tb_Real,   Tb_Real
  | Tb_String, Tb_String => true
  | _, _ => false
  end.




Definition T_h_eqb (t1 t2 : T_h) : bool :=
  match t1, t2 with
  | Th_Basic b1, Th_Basic b2 =>
      T_b_eqb b1 b2
  | Th_Object c1, Th_Object c2 =>
      String.eqb c1 c2
  | _, _ => false
  end.




Definition T_e_eqb (t1 t2 : T_e) : bool :=
  match t1, t2 with
  | Te_Single h1, Te_Single h2 =>
      T_h_eqb h1 h2
  | Te_Bag h1, Te_Bag h2 =>
      T_h_eqb h1 h2
  | _, _ => false
  end.





Definition context := partial_map T_h.





Inductive has_type : context -> object_model -> tm -> T_e -> Prop :=

    (* ======================== Var 表达式 ======================== *)

    | T_Var :
        forall Gamma M x th,
            Gamma x = Some th ->
            has_type Gamma M (CVar x) (Te_Single th)



    (* ======================== operation 表达式 ======================== *)
    (*  无参operation： 字面量构造器  *)

    | T_Lit :
        forall Gamma M ib tb,
            vhas_type_b ib tb ->
            has_type Gamma M (CLit ib) (Te_Single (Th_Basic tb))





    (*  basic type 有参operation： 一元操作  *)
    | T_Unop :
        forall Gamma M op tm te te',
            has_type Gamma M tm te ->
            unop_type op te = Some te' ->
            has_type Gamma M (CUnop op tm) te'




    (*  basic type 有参operation： 二元操作  *)

    | T_Binop :
        forall Gamma M op t1 t2 te1 te2 te',
            has_type Gamma M t1 te1 ->
            has_type Gamma M t2 te2 ->
            binop_type op te1 te2 = Some te' ->
            has_type Gamma M (CBinop op t1 t2) te'





    (*  object type 有参operation： allInstances, 对象属性/角色  *)

    | T_AllInstances :
        forall Gamma M cn,
        has_type Gamma M (CAllInstances cn) (Te_Bag (Th_Object cn))



    | T_Attr :
        forall Gamma M t c attr T,
            has_type Gamma M t (Te_Single (Th_Object c)) ->
            lookup_attr_type M c attr = Some T ->
            has_type Gamma M (CAttr t attr) (Te_Single (Th_Basic T))


    | T_Role :
        forall Gamma M t c1 c2 role,
            has_type Gamma M t (Te_Single (Th_Object c1)) ->
            lookup_role_type M c1 role = Some c2 ->
            has_type Gamma M (CRole t role) (Te_Single (Th_Object c2))



    | T_NRole :
        forall Gamma M t c1 c2 nrole,
            has_type Gamma M t (Te_Single (Th_Object c1)) ->
            lookup_role_type M c1 nrole = Some c2 ->
            has_type Gamma M (CNRole t nrole) (Te_Single (Th_Object c2)) 




    (*  Bag type 有参operation： 字面量构造器 *)
    | T_BagLiteral :
        forall Gamma M vs Tb,
        (forall v, In v vs -> Ib_type v = Tb) ->
        has_type Gamma M (CBagLiteral Tb vs) (Te_Bag (Th_Basic Tb))




    (*  Bag type 有参operation： Bag 集合运算  *)
    | T_Union :
        forall Gamma M t1 t2 T,
            has_type Gamma M t1 (Te_Bag T) ->
            has_type Gamma M t2 (Te_Bag T) ->
            has_type Gamma M (CUnion t1 t2) (Te_Bag T)


    | T_Difference :
        forall Gamma M t1 t2 T,
            has_type Gamma M t1 (Te_Bag T) ->
            has_type Gamma M t2 (Te_Bag T) ->
            has_type Gamma M (CDifference t1 t2) (Te_Bag T)



    (*  Bag type 有参operation： Bag 函数  *)
    | T_CAggregate :
        forall Gamma M op tm th th',
            has_type Gamma M tm (Te_Bag th) ->
            aggop_type op th = Some th' ->
            has_type Gamma M (CAggregate op tm) (Te_Single th')



    (* ======================== iterator 表达式 ======================== *)

    (*  Bag type 有参operation：Iterator（绑定变量！）*)


    | T_Select :
        forall Gamma M t x T body,
            has_type Gamma M t (Te_Bag T) ->
            has_type (update Gamma x T) M body (Te_Single (Th_Basic Tb_Bool)) ->
            has_type Gamma M (CSelect t x body) (Te_Bag T)
    




.