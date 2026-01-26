

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









Definition context := partial_map T_h.





Inductive has_type : context -> object_model -> tm -> T_e -> Prop :=

    (* ======================== Var 表达式 ======================== *)

    | T_Var :
        forall Gamma M x th,
            Gamma x = Some th ->
            has_type Gamma M (CVar x) (Te_Single th)



    (* ======================== operation 表达式 ======================== *)
    (*  无参operation： 字面量构造器  *)

    | T_Bool :
        forall Gamma M b,
            has_type Gamma M (CBool b) (Te_Single (Th_Basic Tb_Bool))

    | T_Int :
        forall Gamma M n,
            has_type Gamma M (CInt n) (Te_Single (Th_Basic Tb_Int))

    | T_Real :
        forall Gamma M r,
            has_type Gamma M (CReal r) (Te_Single (Th_Basic Tb_Real))

    | T_String :
        forall Gamma M s,
            has_type Gamma M (CString s) (Te_Single (Th_Basic Tb_String))




    (*  basic type 有参operation： 一元操作  *)
    | T_BoolUn :
        forall Gamma M op t,
            has_type Gamma M t (Te_Single (Th_Basic Tb_Bool)) ->
            has_type Gamma M (CBoolUn op t) (Te_Single (Th_Basic Tb_Bool))



    | T_ArithUn_Int :
        forall Gamma M op t,
            (op = UNeg \/ op = UAbs) ->
            has_type Gamma M t (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma M (CArithUn op t) (Te_Single (Th_Basic Tb_Int))


    | T_ArithUn_Real :
        forall Gamma M op t,
            (op = UNeg \/ op = UAbs) ->
            has_type Gamma M t (Te_Single (Th_Basic Tb_Real)) ->
            has_type Gamma M (CArithUn op t) (Te_Single (Th_Basic Tb_Real))


    | T_ArithUn_ToInt :
        forall Gamma M op t,
            (op = UFloor \/ op = URound) ->
            has_type Gamma M t (Te_Single (Th_Basic Tb_Real)) ->
            has_type Gamma M (CArithUn op t) (Te_Single (Th_Basic Tb_Int))


    | T_StrUn :
        forall Gamma M op t,
            has_type Gamma M t (Te_Single (Th_Basic Tb_String)) ->
            has_type Gamma M (CStrUn op t) (Te_Single (Th_Basic Tb_String))



    | T_Substring :
        forall Gamma M t i j,
            has_type Gamma M t (Te_Single (Th_Basic Tb_String)) ->
            has_type Gamma M (CSubstring t i j) (Te_Single (Th_Basic Tb_String)) 






    (*  basic type 有参operation： 二元操作  *)

    | T_BoolBin :
        forall Gamma M op t1 t2,
            has_type Gamma M t1 (Te_Single (Th_Basic Tb_Bool)) ->
            has_type Gamma M t2 (Te_Single (Th_Basic Tb_Bool)) ->
            has_type Gamma M (CBoolBin op t1 t2) (Te_Single (Th_Basic Tb_Bool))

    (* 
    允许 Object = Object
    不在 typing 层区分可比性（可在语义层或额外约束）
    *)
    | T_CompBin :
        forall Gamma M op t1 t2 th,
            has_type Gamma M t1 (Te_Single th) ->
            has_type Gamma M t2 (Te_Single th) ->
            has_type Gamma M (CCompBin op t1 t2) (Te_Single (Th_Basic Tb_Bool))


    | T_ArithBin_Int :
        forall Gamma M op t1 t2,
            (op = BAdd \/ op = BSub \/ op = BMul)  ->  (* 不是除法 *)
            has_type Gamma M t1 (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma M t2 (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma M (CArithBin op t1 t2) (Te_Single (Th_Basic Tb_Int))


    | T_ArithBin_IntDiv :
        forall Gamma M t1 t2,
            has_type Gamma M t1 (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma M t2 (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma M (CArithBin BDiv t1 t2) (Te_Single (Th_Basic Tb_Real))


    | T_ArithBin_Real :
        forall Gamma M op t1 t2,
            has_type Gamma M t1 (Te_Single (Th_Basic Tb_Real)) ->
            has_type Gamma M t2 (Te_Single (Th_Basic Tb_Real)) ->
            has_type Gamma M (CArithBin op t1 t2) (Te_Single (Th_Basic Tb_Real))



    | T_StrBin :
        forall Gamma M op t1 t2,
            has_type Gamma M t1 (Te_Single (Th_Basic Tb_String)) ->
            has_type Gamma M t2 (Te_Single (Th_Basic Tb_String)) ->
            has_type Gamma M (CStrBin op t1 t2) (Te_Single (Th_Basic Tb_String))


    | T_AggBin_Int :
        forall Gamma M op t1 t2,
            has_type Gamma M t1 (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma M t2 (Te_Single (Th_Basic Tb_Int)) ->
            has_type Gamma M (CAggBin op t1 t2) (Te_Single (Th_Basic Tb_Int))


    | T_AggBin_Real :
        forall Gamma M op t1 t2,
            has_type Gamma M t1 (Te_Single (Th_Basic Tb_Real)) ->
            has_type Gamma M t2 (Te_Single (Th_Basic Tb_Real)) ->
            has_type Gamma M (CAggBin op t1 t2) (Te_Single (Th_Basic Tb_Real))





    (*  object type 有参operation： allInstances, 对象属性/角色  *)

    | T_AllInstances :
        forall Gamma M cn,
        has_type Gamma M (CAllInstances cn) (Te_Bag (Th_Object cn))



    | T_Attr :
        forall Gamma M t c attr T,
            has_type Gamma M t (Te_Single (Th_Object c)) ->
            lookup_attr_type (ATT_c M) c attr = Some T ->
            has_type Gamma M (CAttr t attr) (Te_Single (Th_Basic T))


    | T_Role :
        forall Gamma M t c1 c2 role,
            has_type Gamma M t (Te_Single (Th_Object c1)) ->
            lookup_role_type (ASSOC M) (associates M) (roles M) c1 role = Some c2 ->
            has_type Gamma M (CRole t role) (Te_Single (Th_Object c2))



    | T_NRole :
        forall Gamma M t c1 c2 nrole,
            has_type Gamma M t (Te_Single (Th_Object c1)) ->
            lookup_role_type (ASSOC M) (associates M) (roles M) c1 nrole = Some c2 ->
            has_type Gamma M (CNRole t nrole) (Te_Single (Th_Object c2)) 




    (*  Bag type 有参operation： 字面量构造器 *)
    | T_BagLiteral :
        forall Gamma M ts Tb,
            (forall t, In t ts -> has_type Gamma M t (Te_Single (Th_Basic Tb))) ->
            has_type Gamma M (CBagLiteral Tb ts) (Te_Bag (Th_Basic Tb))




    (*  Bag type 有参operation： Bag 集合运算  *)
    | T_Union :
        forall Gamma M t1 t2 T,
            has_type Gamma M t1 (Te_Bag T) ->
            has_type Gamma M t2 (Te_Bag T) ->
            has_type Gamma M (CUnion t1 t2) (Te_Bag T)

    | T_Intersect :
        forall Gamma M t1 t2 T,
            has_type Gamma M t1 (Te_Bag T) ->
            has_type Gamma M t2 (Te_Bag T) ->
            has_type Gamma M (CIntersect t1 t2) (Te_Bag T)

    | T_Difference :
        forall Gamma M t1 t2 T,
            has_type Gamma M t1 (Te_Bag T) ->
            has_type Gamma M t2 (Te_Bag T) ->
            has_type Gamma M (CDifference t1 t2) (Te_Bag T)

    | T_SymDiff :
        forall Gamma M t1 t2 T,
            has_type Gamma M t1 (Te_Bag T) ->
            has_type Gamma M t2 (Te_Bag T) ->
            has_type Gamma M (CSymDiff t1 t2) (Te_Bag T)












    (*  Bag type 有参operation： Bag 函数  *)



    | T_IncludesAll :
        forall Gamma M t1 t2 T,
            has_type Gamma M t1 (Te_Bag T) ->
            has_type Gamma M t2 (Te_Bag T) ->
            has_type Gamma M (CIncludesAll t1 t2) (Te_Single (Th_Basic Tb_Bool))
    
    | T_ExcludesAll :
        forall Gamma M t1 t2 T,
            has_type Gamma M t1 (Te_Bag T) ->
            has_type Gamma M t2 (Te_Bag T) ->
            has_type Gamma M (CExcludesAll t1 t2) (Te_Single (Th_Basic Tb_Bool))
    
    | T_Includes :
        forall Gamma M t1 t2 T,
            has_type Gamma M t1 (Te_Bag T) ->
            has_type Gamma M t2 (Te_Single T) ->
            has_type Gamma M (CIncludes t1 t2) (Te_Single (Th_Basic Tb_Bool))

    | T_Excludes :
        forall Gamma M t1 t2 T,
            has_type Gamma M t1 (Te_Bag T) ->
            has_type Gamma M t2 (Te_Single T) ->
            has_type Gamma M (CExcludes t1 t2) (Te_Single (Th_Basic Tb_Bool))


    | T_IsEmpty :
        forall Gamma M t T,
            has_type Gamma M t (Te_Bag T) ->
            has_type Gamma M (CIsEmpty t) (Te_Single (Th_Basic Tb_Bool))

    | T_NotEmpty :
        forall Gamma M t T,
            has_type Gamma M t (Te_Bag T) ->
            has_type Gamma M (CNotEmpty t) (Te_Single (Th_Basic Tb_Bool))

    | T_IsUnique :
        forall Gamma M t T,
            has_type Gamma M t (Te_Bag T) ->
            has_type Gamma M (CIsUnique t) (Te_Single (Th_Basic Tb_Bool))


    | T_CAggregate_Size :
        forall Gamma M t T,
            has_type Gamma M t (Te_Bag T) ->
            has_type Gamma M (CAggregate AggSize t) (Te_Single (Th_Basic Tb_Int))

    | T_CAggregate_Int :
        forall Gamma M op t,
            (op = AggMin \/ op = AggMax \/ op = AggSum) ->
            has_type Gamma M t (Te_Bag (Th_Basic Tb_Int)) ->
            has_type Gamma M (CAggregate op t) (Te_Single (Th_Basic Tb_Int))

    | T_CAggregate_Real :
        forall Gamma M op t,
            (op = AggMin \/ op = AggMax \/ op = AggSum) ->
            has_type Gamma M t (Te_Bag (Th_Basic Tb_Real)) ->
            has_type Gamma M (CAggregate op t) (Te_Single (Th_Basic Tb_Real))




    (* ======================== iterator 表达式 ======================== *)

    (*  Bag type 有参operation：Iterator（绑定变量！）*)

    | T_ForAll :
        forall Gamma M t x T body,
            has_type Gamma M t (Te_Bag T) ->
            has_type (update Gamma x T) M body (Te_Single (Th_Basic Tb_Bool)) ->
            has_type Gamma M (CForAll t x body) (Te_Single (Th_Basic Tb_Bool))

    | T_Exists :
        forall Gamma M t x T body,
            has_type Gamma M t (Te_Bag T) ->
            has_type (update Gamma x T) M body (Te_Single (Th_Basic Tb_Bool)) ->
            has_type Gamma M (CExists t x body) (Te_Single (Th_Basic Tb_Bool))

    (* | T_One :
        forall Gamma M t x T body,
            has_type Gamma M t (Te_Bag T) ->
            has_type (update Gamma x T) M body (Te_Single (Th_Basic Tb_Bool)) ->
            has_type Gamma M (COne t x body) (Te_Single (Th_Basic Tb_Bool)) *)


    | T_Select :
        forall Gamma M t x T body,
            has_type Gamma M t (Te_Bag T) ->
            has_type (update Gamma x T) M body (Te_Single (Th_Basic Tb_Bool)) ->
            has_type Gamma M (CSelect t x body) (Te_Bag T)
    
    | T_Reject :
        forall Gamma M t x T body,
            has_type Gamma M t (Te_Bag T) ->
            has_type (update Gamma x T) M body (Te_Single (Th_Basic Tb_Bool)) ->
            has_type Gamma M (CReject t x body) (Te_Bag T)
        

        
    | T_Collect :
        forall Gamma M t c attr T,
            has_type Gamma M t (Te_Bag (Th_Object c)) ->
            lookup_attr_type (ATT_c M) c attr = Some T ->
            has_type Gamma M (CCollect t attr) (Te_Bag (Th_Basic T))
        
    | T_RCollect :
        forall Gamma M t c1 c2 role,
            has_type Gamma M t (Te_Bag (Th_Object c1)) ->
            lookup_role_type (ASSOC M) (associates M) (roles M) c1 role = Some c2 ->
            has_type Gamma M (CRCollect t role) (Te_Bag (Th_Object c2))

    | T_NRCollect :
        forall Gamma M t c1 c2 nrole,
            has_type Gamma M t (Te_Bag (Th_Object c1)) ->
            lookup_role_type (ASSOC M) (associates M) (roles M) c1 nrole = Some c2 ->
            has_type Gamma M (CNRCollect t nrole) (Te_Bag (Th_Object c2))




    (*  context *)

    | T_Context :
        forall Gamma M cn body,
            has_type (update Gamma "self" (Th_Object cn)) M body (Te_Single (Th_Basic Tb_Bool)) ->
            has_type Gamma M (CContext cn body) (Te_Single (Th_Basic Tb_Bool))



.