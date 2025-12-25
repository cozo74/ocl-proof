

From Stdlib Require Import String ZArith Reals List.
Import ListNotations.

From OCL Require Import Types Syntax Utils Semantic.
Open Scope string_scope.

(* ================================= Typing ======================================= *)


Inductive vhas_type (M : obj_model) : value -> ty -> Prop :=

    | VT_Bool :
        forall b,
            vhas_type M (V_Bool b) Ty_Bool

    | VT_Int :
        forall n,
            vhas_type M (V_Int n) Ty_Int

    | VT_Real :
        forall r,
            vhas_type M (V_Real r) Ty_Real

    | VT_String :
        forall s,
            vhas_type M (V_String s) Ty_String

    | VT_Object :
        forall oid,
            vhas_type M (V_Object oid) (Ty_Object (cname (objects M oid)))

    | VT_Bag :
        forall vs T,
            (forall v, In v vs -> vhas_type M v T) ->
            vhas_type M (V_Bag vs) (Ty_Bag T).










Definition attr_key (cn a : string) : string :=
  cn ++ "." ++ a.

Definition role_key (cn r : string) : string :=
  cn ++ "." ++ r.

Definition nrole_key (cn nr : string) : string :=
  cn ++ "." ++ nr.




Definition context := total_map ty.



Inductive has_type : context -> tm -> ty -> Prop :=




(*  字面量  *)

    | T_Bool :
        forall Gamma b,
            has_type Gamma (CBool b) Ty_Bool

    | T_Int :
        forall Gamma n,
            has_type Gamma (CInt n) Ty_Int

    | T_Real :
        forall Gamma r,
            has_type Gamma (CReal r) Ty_Real

    | T_String :
        forall Gamma s,
            has_type Gamma (CString s) Ty_String

    (* | T_Object :
        forall Gamma cn,
            has_type Gamma (CObject oid) (Ty_Object cn) *)

(*  集合（Bag） *)

    | T_EmptyBag :
        forall Gamma T,
            has_type Gamma (CEmptyBag T) (Ty_Bag T) 


    | T_BagLiteral :
        forall Gamma ts T,
            (forall t, In t ts -> has_type Gamma t T) ->
            has_type Gamma (CBagLiteral ts) (Ty_Bag T)

(*  context *)

    | T_Context :
        forall Gamma cn body,
            has_type (t_update Gamma "self" (Ty_Object cn)) body Ty_Bool ->
            has_type Gamma (CContext cn body) Ty_Bool



(*  Var Self  *)

    | T_Var :
        forall Gamma x T,
            Gamma x = T ->
            has_type Gamma (CVar x) T

    | T_Self :
        forall Gamma cn,
            Gamma "self" = Ty_Object cn ->
            has_type Gamma CSelf (Ty_Object cn)

(*  对象 / 属性 / 角色  *)

    | T_Attr :
        forall Gamma t cn attr T,
            has_type Gamma t (Ty_Object cn) ->
            Gamma (attr_key cn attr) = T ->
            has_type Gamma (CAttr t attr) T


    | T_Role :
        forall Gamma t cn r T,
            has_type Gamma t (Ty_Object cn) ->
            Gamma (role_key cn r) = Ty_Object T ->
            has_type Gamma (CRole t r) (Ty_Object T)



    | T_NRole :
        forall Gamma t cn r T,
            has_type Gamma t (Ty_Object cn) ->
            Gamma (nrole_key cn r) = Ty_Bag (Ty_Object T) ->
            has_type Gamma (CNRole t r) (Ty_Bag (Ty_Object T))


(*  allInstances  *)

    | T_AllInstances :
        forall Gamma cn,
        has_type Gamma (CAllInstances cn) (Ty_Bag (Ty_Object cn))


(*  一元操作  *)

    | T_BoolUn :
        forall Gamma op t,
            has_type Gamma t Ty_Bool ->
            has_type Gamma (CBoolUn op t) Ty_Bool


    | T_ArithUn_Int :
        forall Gamma op t,
            (op = UNeg \/ op = UAbs) ->
            has_type Gamma t Ty_Int ->
            has_type Gamma (CArithUn op t) Ty_Int
        
    | T_ArithUn_Real :
        forall Gamma op t,
            (op = UNeg \/ op = UAbs) ->
            has_type Gamma t Ty_Real ->
            has_type Gamma (CArithUn op t) Ty_Real
    
    | T_ArithUn_ToInt :
        forall Gamma op t,
            (op = UFloor \/ op = URound) ->
            has_type Gamma t Ty_Real ->
            has_type Gamma (CArithUn op t) Ty_Int


    | T_StrUn :
        forall Gamma op t,
            has_type Gamma t Ty_String ->
            has_type Gamma (CStrUn op t) Ty_String


(*  二元操作  *)


    | T_BoolBin :
        forall Gamma op t1 t2,
            has_type Gamma t1 Ty_Bool ->
            has_type Gamma t2 Ty_Bool ->
            has_type Gamma (CBoolBin op t1 t2) Ty_Bool

(* 
    允许 Object = Object
    不在 typing 层区分可比性（可在语义层或额外约束）
 *)
    | T_CompBin :
        forall Gamma op t1 t2 T,
            has_type Gamma t1 T ->
            has_type Gamma t2 T ->
            has_type Gamma (CCompBin op t1 t2) Ty_Bool


    | T_ArithBin_Int :
        forall Gamma op t1 t2,
            (op = BAdd \/ op = BSub \/ op = BMul)  ->  (* 不是除法 *)
            has_type Gamma t1 Ty_Int ->
            has_type Gamma t2 Ty_Int ->
            has_type Gamma (CArithBin op t1 t2) Ty_Int
        

    | T_ArithBin_IntDiv :
        forall Gamma t1 t2,
            has_type Gamma t1 Ty_Int ->
            has_type Gamma t2 Ty_Int ->
            has_type Gamma (CArithBin BDiv t1 t2) Ty_Real


    | T_ArithBin_Real :
        forall Gamma op t1 t2,
            has_type Gamma t1 Ty_Real ->
            has_type Gamma t2 Ty_Real ->
            has_type Gamma (CArithBin op t1 t2) Ty_Real



    | T_StrBin :
        forall Gamma op t1 t2,
            has_type Gamma t1 Ty_String ->
            has_type Gamma t2 Ty_String ->
            has_type Gamma (CStrBin op t1 t2) Ty_String


    | T_AggBin_Int :
        forall Gamma op t1 t2,
        has_type Gamma t1 Ty_Int ->
        has_type Gamma t2 Ty_Int ->
        has_type Gamma (CAggBin op t1 t2) Ty_Int


    | T_AggBin_Real :
        forall Gamma op t1 t2,
        has_type Gamma t1 Ty_Real ->
        has_type Gamma t2 Ty_Real ->
        has_type Gamma (CAggBin op t1 t2) Ty_Real


(*  Bag 运算  *)

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


(*  Bag 谓词  *)


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


(*  Iterator（绑定变量！）*)

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
        
    | T_One :
        forall Gamma t x T body,
            has_type Gamma t (Ty_Bag T) ->
            has_type (t_update Gamma x T) body Ty_Bool ->
            has_type Gamma (COne t x body) Ty_Bool
        
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

(*  bag聚合  *)

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


(* String ops with integer arguments *)

    | T_EAt :
        forall Gamma t i,
            has_type Gamma t Ty_String ->
            has_type Gamma (EAt t i) Ty_String

    | T_ESubstring :
        forall Gamma t i j,
            has_type Gamma t Ty_String ->
            has_type Gamma (ESubstring t i j) Ty_String .