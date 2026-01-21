

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
        forall o cn,
        vhas_type_h (Ih_Object o) (Th_Object cn).




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









Definition attr_key (cn a : string) : string :=
  cn ++ "." ++ a.

Definition role_key (cn r : string) : string :=
  cn ++ "." ++ r.

Definition nrole_key (cn nr : string) : string :=
  cn ++ "." ++ nr.





Definition context := partial_map T_h.





Inductive has_type : context -> tm -> T_e -> Prop :=

    (* ======================== Var 表达式 ======================== *)

    | T_Var :
        forall Gamma x th,
            Gamma x = Some th ->
            has_type Gamma (CVar x) (Te_Single th)



    (* ======================== operation 表达式 ======================== *)
    (*  无参operation： 字面量构造器  *)

    | T_Bool :
        forall Gamma b,
            has_type Gamma (CBool b) (Te_Single (Th_Basic Tb_Bool))

    | T_Int :
        forall Gamma n,
            has_type Gamma (CInt n) (Te_Single (Th_Basic Tb_Int))

    | T_Real :
        forall Gamma r,
            has_type Gamma (CReal r) (Te_Single (Th_Basic Tb_Real))

    | T_String :
        forall Gamma s,
            has_type Gamma (CString s) (Te_Single (Th_Basic Tb_String))




    (*  basic type 有参operation： 一元操作  *)
    | T_BoolUn :
        forall Gamma op t,
            has_type Gamma t (Te_Single (Th_Basic Tb_Bool)) ->
            has_type Gamma (CBoolUn op t) (Te_Single (Th_Basic Tb_Bool))



    | T_ArithUn_Int :
        forall Gamma op t,
            (op = UNeg \/ op = UAbs) ->
            has_type Gamma t (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma (CArithUn op t) (Te_Single (Th_Basic Tb_Int))


    | T_ArithUn_Real :
        forall Gamma op t,
            (op = UNeg \/ op = UAbs) ->
            has_type Gamma t (Te_Single (Th_Basic Tb_Real)) ->
            has_type Gamma (CArithUn op t) (Te_Single (Th_Basic Tb_Real))


    | T_ArithUn_ToInt :
        forall Gamma op t,
            (op = UFloor \/ op = URound) ->
            has_type Gamma t (Te_Single (Th_Basic Tb_Real)) ->
            has_type Gamma (CArithUn op t) (Te_Single (Th_Basic Tb_Int))


    | T_StrUn :
        forall Gamma op t,
            has_type Gamma t (Te_Single (Th_Basic Tb_String)) ->
            has_type Gamma (CStrUn op t) (Te_Single (Th_Basic Tb_String))



    | T_ESubstring :
        forall Gamma t i j,
            has_type Gamma t (Te_Single (Th_Basic Tb_String)) ->
            has_type Gamma (ESubstring t i j) (Te_Single (Th_Basic Tb_String)) 






    (*  basic type 有参operation： 二元操作  *)

    | T_BoolBin :
        forall Gamma op t1 t2,
            has_type Gamma t1 (Te_Single (Th_Basic Tb_Bool)) ->
            has_type Gamma t2 (Te_Single (Th_Basic Tb_Bool)) ->
            has_type Gamma (CBoolBin op t1 t2) (Te_Single (Th_Basic Tb_Bool))

    (* 
    允许 Object = Object
    不在 typing 层区分可比性（可在语义层或额外约束）
    *)
    | T_CompBin :
        forall Gamma op t1 t2 T,
            has_type Gamma t1 (Te_Single th) ->
            has_type Gamma t2 (Te_Single th) ->
            has_type Gamma (CCompBin op t1 t2) (Te_Single (Th_Basic Tb_Bool))


    | T_ArithBin_Int :
        forall Gamma op t1 t2,
            (op = BAdd \/ op = BSub \/ op = BMul)  ->  (* 不是除法 *)
            has_type Gamma t1 (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma t2 (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma (CArithBin op t1 t2) (Te_Single (Th_Basic Tb_Int))


    | T_ArithBin_IntDiv :
        forall Gamma t1 t2,
            has_type Gamma t1 (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma t2 (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma (CArithBin BDiv t1 t2) (Te_Single (Th_Basic Tb_Real))


    | T_ArithBin_Real :
        forall Gamma op t1 t2,
            has_type Gamma t1 (Te_Single (Th_Basic Tb_Real)) ->
            has_type Gamma t2 (Te_Single (Th_Basic Tb_Real)) ->
            has_type Gamma (CArithBin op t1 t2) (Te_Single (Th_Basic Tb_Real))



    | T_StrBin :
        forall Gamma op t1 t2,
            has_type Gamma t1 (Te_Single (Th_Basic Tb_String)) ->
            has_type Gamma t2 (Te_Single (Th_Basic Tb_String)) ->
            has_type Gamma (CStrBin op t1 t2) (Te_Single (Th_Basic Tb_String))


    | T_AggBin_Int :
        forall Gamma op t1 t2,
            has_type Gamma t1 (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma t2 (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma (CAggBin op t1 t2) (Te_Single (Th_Basic Tb_Int))


    | T_AggBin_Real :
        forall Gamma op t1 t2,
            has_type Gamma t1 (Te_Single (Th_Basic Tb_Real)) ->
            has_type Gamma t2 (Te_Single (Th_Basic Tb_Real)) ->
            has_type Gamma (CAggBin op t1 t2) (Te_Single (Th_Basic Tb_Real))





    (*  object type 有参operation： allInstances, 对象属性/角色  *)

    | T_AllInstances :
        forall Gamma cn,
        has_type Gamma (CAllInstances cn) (Te_Bag (Th_Object cn))



    | T_Attr :
        forall Gamma t cn attr T,
            has_type Gamma t (Te_Single (Th_Object c)) ->
            Gamma (attr_key c attr) = Some T ->
            has_type Gamma (CAttr t attr) (Te_Single (Th_Basic T))


    | T_Role :
        forall Gamma t c1 r T,
            has_type Gamma t (Te_Single (Th_Object c1)) ->
            Gamma (role_key c1 r) = (Te_Single (Th_Object c2)) ->
            has_type Gamma (CRole t r) (Te_Single (Th_Object c2))



    | T_NRole :
        forall Gamma t cn r T,
            has_type Gamma t (Ty_Object cn) ->
            Gamma (nrole_key cn r) = Ty_Bag (Ty_Object T) ->
            has_type Gamma (CNRole t r) (Ty_Bag (Ty_Object T))




    (*  Bag type 有参operation： 字面量构造器 *)
    | T_BagLiteral :
        forall Gamma ts T,
            (forall t, In t ts -> has_type Gamma t T) ->
            has_type Gamma (CBagLiteral ts) (Ty_Bag T)




    (*  Bag type 有参operation： Bag 集合运算  *)
    | T_Union :
        forall Gamma t1 t2 T,
            has_type Gamma t1 (Ty_Bag T) ->
            has_type Gamma t2 (Ty_Bag T) ->
            has_type Gamma (CUnion t1 t2) (Ty_Bag T)

    | T_Intersect :
        forall Gamma t1 t2 T,
            has_type Gamma t1 (Ty_Bag T) ->
            has_type Gamma t2 (Ty_Bag T) ->
            has_type Gamma (CIntersect t1 t2) (Ty_Bag T)

    | T_Difference :
        forall Gamma t1 t2 T,
            has_type Gamma t1 (Ty_Bag T) ->
            has_type Gamma t2 (Ty_Bag T) ->
            has_type Gamma (CDifference t1 t2) (Ty_Bag T)

    | T_SymDiff :
        forall Gamma t1 t2 T,
            has_type Gamma t1 (Ty_Bag T) ->
            has_type Gamma t2 (Ty_Bag T) ->
            has_type Gamma (CSymDiff t1 t2) (Ty_Bag T)












    (*  Bag type 有参operation： Bag 函数  *)



    | T_IncludesAll :
        forall Gamma t1 t2 T,
            has_type Gamma t1 (Ty_Bag T) ->
            has_type Gamma t2 (Ty_Bag T) ->
            has_type Gamma (CIncludesAll t1 t2) Ty_Bool
    
    | T_ExcludesAll :
        forall Gamma t1 t2 T,
            has_type Gamma t1 (Ty_Bag T) ->
            has_type Gamma t2 (Ty_Bag T) ->
            has_type Gamma (CExcludesAll t1 t2) Ty_Bool
    
    | T_Includes :
        forall Gamma t1 t2 T,
            has_type Gamma t1 (Ty_Bag T) ->
            has_type Gamma t2 T ->
            has_type Gamma (CIncludes t1 t2) Ty_Bool

    | T_Excludes :
        forall Gamma t1 t2 T,
            has_type Gamma t1 (Ty_Bag T) ->
            has_type Gamma t2 T ->
            has_type Gamma (CExcludes t1 t2) Ty_Bool


    | T_IsEmpty :
        forall Gamma t T,
            has_type Gamma t (Ty_Bag T) ->
            has_type Gamma (CIsEmpty t) Ty_Bool

    | T_NotEmpty :
        forall Gamma t T,
            has_type Gamma t (Ty_Bag T) ->
            has_type Gamma (CNotEmpty t) Ty_Bool

    | T_IsUnique :
        forall Gamma t T,
            has_type Gamma t (Ty_Bag T) ->
            has_type Gamma (CIsUnique t) Ty_Bool


    | T_EAggregate_Size :
        forall Gamma t T,
            has_type Gamma t (Ty_Bag T) ->
            has_type Gamma (EAggregate AggSize t) Ty_Int

    | T_EAggregate_Int :
        forall Gamma op t,
            (op = AggMin \/ op = AggMax \/ op = AggSum) ->
            has_type Gamma t (Ty_Bag Ty_Int) ->
            has_type Gamma (EAggregate op t) Ty_Int

    | T_EAggregate_Real :
        forall Gamma op t,
            (op = AggMin \/ op = AggMax \/ op = AggSum) ->
            has_type Gamma t (Ty_Bag Ty_Real) ->
            has_type Gamma (EAggregate op t) Ty_Real




    (* ======================== iterator 表达式 ======================== *)

    (*  Bag type 有参operation：Iterator（绑定变量！）*)

    | T_ForAll :
        forall Gamma t x T body,
            has_type Gamma t (Ty_Bag T) ->
            has_type (t_update Gamma x T) body Ty_Bool ->
            has_type Gamma (CForAll t x body) Ty_Bool

    | T_Exists :
        forall Gamma t x T body,
            has_type Gamma t (Ty_Bag T) ->
            has_type (t_update Gamma x T) body Ty_Bool ->
            has_type Gamma (CExists t x body) Ty_Bool

    | T_One :
        forall Gamma t x T body,
            has_type Gamma t (Ty_Bag T) ->
            has_type (t_update Gamma x T) body Ty_Bool ->
            has_type Gamma (COne t x body) Ty_Bool


    | T_Select :
        forall Gamma t x T body,
            has_type Gamma t (Ty_Bag T) ->
            has_type (t_update Gamma x T) body Ty_Bool ->
            has_type Gamma (CSelect t x body) (Ty_Bag T)
    
    | T_Reject :
        forall Gamma t x T body,
            has_type Gamma t (Ty_Bag T) ->
            has_type (t_update Gamma x T) body Ty_Bool ->
            has_type Gamma (CReject t x body) (Ty_Bag T)
        

        
    | T_Collect :
        forall Gamma t cn a T,
            has_type Gamma t (Ty_Bag (Ty_Object cn)) ->
            Gamma (attr_key cn a) = T ->
            has_type Gamma (CCollect t a) (Ty_Bag T)
        
    | T_RCollect :
        forall Gamma t cn r C,
            has_type Gamma t (Ty_Bag (Ty_Object cn)) ->
            Gamma (role_key cn r) = Ty_Object C ->
            has_type Gamma (CRCollect t r) (Ty_Bag (Ty_Object C))
    
    | T_NRCollect :
        forall Gamma t cn r C,
            has_type Gamma t (Ty_Bag (Ty_Object cn)) ->
            Gamma (nrole_key cn r) = Ty_Bag (Ty_Object C) ->
            has_type Gamma (CNRCollect t r) (Ty_Bag (Ty_Object C))





    (*  context *)

    | T_Context :
        forall Gamma cn body,
            has_type (t_update Gamma "self" (Ty_Object cn)) body Ty_Bool ->
            has_type Gamma (CContext cn body) Ty_Bool



.