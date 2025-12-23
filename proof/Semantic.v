
From Stdlib Require Import String ZArith Reals List.
Import ListNotations.

From OCL Require Import Types Syntax Utils.
Open Scope string_scope.

(* ================================= Operational Semantics ======================================= *)


Definition total_map (A : Type) := string -> A.
Definition empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition update {A : Type} (m : total_map A)
  (x : string) (v : A) :=
fun x' => if String.eqb x x' then v else m x'.





Inductive value : Type :=
  | V_Bool      : bool -> value
  | V_Int       : Z -> value
  | V_Real      : R -> value
  | V_String    : string -> value
  | V_Object    : string -> value
  | V_Bag       : list value -> value.


Record obj := {
  oid   : string;             (* object identity *)
  cname  : class;              (* object's class name *)
  attrs : total_map value;   (* attribute map *)
  roles : total_map string;  (* association role -> list of target object IDs *)
  nroles : total_map (list string);  (* association role -> list of target object IDs *)
}.

Record obj_model := {
  objects : total_map obj;   (* object id -> object *)
  cmap : total_map (list string);
}.


Definition env := total_map value.     (* var name -> valu *)






Inductive ceval : obj_model -> env -> tm -> value -> Prop :=

  (* context C inv body 语义：对所有实例执行 forAll *)
      | E_CContext :
          forall M E C body v,
          ceval M E (CForAll (CAllInstances C) "self" body) v ->
          ceval M E (CContext C body) v
      
(*       

  (* Var Self *)
      | E_Var :
          forall M E var,
          ceval M E (CVar var) (E var)

      | E_Self :
          forall M E,
          ceval M E CSelf (E "self")

  (* 一元运算 *)
      
      | E_BoolUnUNotTru :
        forall M E,
        ceval M E (CBoolUn UNot (CBool true)) (CBool false )


      | E_BoolUnUNotFls :
        forall M E,
        ceval M E (CBoolUn UNot (CBool false)) (CBool true)


      | E_ArithUnIntUNeg :
        forall M E n,
        ceval M E (CArithUn UNeg (CInt n)) ( CInt (-n))

      | E_ArithUnIntUAbs :
        forall M E n,
        ceval M E (CArithUn UAbs (CInt n)) ( CInt (Z.abs n))


      | E_ArithUnRealUNeg :
        forall M E r,
        ceval M E (CArithUn UNeg (CReal r)) ( CReal (-r))

      | E_ArithUnRealUAbs :
        forall M E r,
        ceval M E (CArithUn UAbs (CReal r)) ( CReal (Rabs r))

      | E_ArithUnRealUFloor :
        forall M E r z,
        Rfloor_real r z ->
        ceval M E (CArithUn UFloor (CReal r)) ( CInt z)

      | E_ArithUnRealURound :
        forall M E r z,
        Rround_real r z ->
        ceval M E (CArithUn URound (CReal r)) ( CInt z)


      | E_StrUnUToUpper :
        forall M E s,
        ceval M E (CStrUn UToUpper (CString s)) ( CString (toUpper s) )

      | E_StrUnUToLower :
        forall M E s,
        ceval M E (CStrUn UToLower (CString s)) ( CString (toLower s) )

  (* 二元运算 *)

    (* 二元逻辑运算 *)
      | E_BoolBinBAnd : 
        forall M E a b,
        ceval M E (CBoolBin BAnd (CBool a) (CBool b)) (CBool (andb a b) ) 

      | E_BoolBinBOr : 
        forall M E a b,
        ceval M E (CBoolBin BOr (CBool a) (CBool b)) (CBool (orb a b) ) 

      | E_BoolBinBXor : 
        forall M E a b,
        ceval M E (CBoolBin BXor (CBool a) (CBool b)) (CBool (xorb a b) ) 

      | E_BoolBinBImplies : 
        forall M E a b,
        ceval M E (CBoolBin BImplies (CBool a) (CBool b)) (CBool (orb (negb a) b) ) 

    (* 二元比较运算 *)

      | E_CompBinBEq :
        forall M E a b,
        ceval M E (CCompBin BEq (CInt a) (CInt b)) (CBool (a =? b)%Z)


      | E_CompBinBEq1 :
        forall M E a b,
        ceval M E (CCompBin BEq (CInt a) (CReal b)) (CBool (Reqb (IZR a) (b)) )

      | E_CompBinBEq2 :
        forall M E a b,
        ceval M E (CCompBin BEq (CReal a) (CReal b)) (CBool (Reqb a b) )

      | E_CompBinBEq3 :
        forall M E a b,
        ceval M E (CCompBin BEq (CString a) (CString b)) (CBool (String.eqb a b) )

      | E_CompBinBEq4 :
        forall M E a b,
        ceval M E (CCompBin BEq (CObject a) (CObject b)) (CBool (String.eqb a b) )




      | E_CompBinBNe :
        forall M E a b,
        ceval M E (CCompBin BNe (CInt a) (CInt b)) (CBool (negb (a =? b)%Z))


      | E_CompBinBNe1 :
        forall M E a b,
        ceval M E (CCompBin BNe (CInt a) (CReal b)) (CBool (Rneqb (IZR a) (b)) )

      | E_CompBinBNe2 :
        forall M E a b,
        ceval M E (CCompBin BNe (CReal a) (CReal b)) (CBool (Rneqb a b) )


      | E_CompBinBNe3 :
        forall M E a b,
        ceval M E (CCompBin BEq (CString a) (CString b)) (CBool (negb (String.eqb a b)) )



      | E_CompBinBNe4 :
        forall M E a b,
        ceval M E (CCompBin BEq (CObject a) (CObject b)) (CBool (negb (String.eqb a b)) )




      | E_CompBinBLt :
        forall M E a b,
        ceval M E (CCompBin BLt (CInt a) (CInt b)) (CBool (a <? b)%Z)


      | E_CompBinBLt1 :
        forall M E a b,
        ceval M E (CCompBin BLt (CInt a) (CReal b)) (CBool (Rltb (IZR a) (b)) )

      | E_CompBinBLt2 :
        forall M E a b,
        ceval M E (CCompBin BLt (CReal a) (CReal b)) (CBool (Rltb a b) )

      | E_CompBinBLe :
        forall M E a b,
        ceval M E (CCompBin BLe (CInt a) (CInt b)) (CBool (a <=? b)%Z)


      | E_CompBinBLe1 :
        forall M E a b,
        ceval M E (CCompBin BLe (CInt a) (CReal b)) (CBool (Rleb (IZR a) (b)) )

      | E_CompBinBLe2 :
        forall M E a b,
        ceval M E (CCompBin BLe (CReal a) (CReal b)) (CBool (Rleb a b) )


      | E_CompBinBGt :
        forall M E a b,
        ceval M E (CCompBin BGt (CInt a) (CInt b)) (CBool (a >? b)%Z)


      | E_CompBinBGt1 :
        forall M E a b,
        ceval M E (CCompBin BGt (CInt a) (CReal b)) (CBool (Rgtb (IZR a) (b)) )

      | E_CompBinBGt2 :
        forall M E a b,
        ceval M E (CCompBin BGt (CReal a) (CReal b)) (CBool (Rgtb a b) )


      | E_CompBinBGe :
        forall M E a b,
        ceval M E (CCompBin BGe (CInt a) (CInt b)) (CBool (a >=? b)%Z)


      | E_CompBinBGe1 :
        forall M E a b,
        ceval M E (CCompBin BGe (CInt a) (CReal b)) (CBool (Rgeb (IZR a) (b)) )

      | E_CompBinBGe2 :
        forall M E a b,
        ceval M E (CCompBin BGe (CReal a) (CReal b)) (CBool (Rgeb a b) )


    (* 二元算数运算 *)

      | E_ArithBinBAdd :
        forall M E a b,
        ceval M E (CArithBin BAdd (CInt a) (CInt b)) (CInt (a + b)%Z)

      | E_ArithBinBAdd1 :
        forall M E a b,
        ceval M E (CArithBin BAdd (CInt a) (CReal b)) (CReal (IZR a + b)%R)

      | E_ArithBinBAdd2 :
        forall M E a b,
        ceval M E (CArithBin BAdd (CReal a) (CReal b)) (CReal (a + b)%R)


      | E_ArithBinBSub :
        forall M E a b,
        ceval M E (CArithBin BSub (CInt a) (CInt b)) (CInt (a - b)%Z)

      | E_ArithBinBSub1 :
        forall M E a b,
        ceval M E (CArithBin BSub (CInt a) (CReal b)) (CReal (IZR a - b)%R)

      | E_ArithBinBSub2 :
        forall M E a b,
        ceval M E (CArithBin BSub (CReal a) (CReal b)) (CReal (a - b)%R)


      | E_ArithBinBMul :
        forall M E a b,
        ceval M E (CArithBin BMul (CInt a) (CInt b)) (CInt (a * b)%Z)

      | E_ArithBinBMul1 :
        forall M E a b,
        ceval M E (CArithBin BMul (CInt a) (CReal b)) (CReal (IZR a * b)%R)

      | E_ArithBinBMul2 :
        forall M E a b,
        ceval M E (CArithBin BMul (CReal a) (CReal b)) (CReal (a * b)%R)


      | E_ArithBinBDiv :
        forall M E a b,
        ceval M E (CArithBin BDiv (CInt a) (CInt b)) (CReal ((IZR a) / (IZR b))%R)

      | E_ArithBinBDiv1 :
        forall M E a b,
        ceval M E (CArithBin BDiv (CInt a) (CReal b)) (CReal (IZR a / b)%R)

      | E_ArithBinBDiv2 :
        forall M E a b,
        ceval M E (CArithBin BDiv (CReal a) (CReal b)) (CReal (a / b)%R)

    (* 二元字符串运算 *)

      | E_StrBinBConcat :
        forall M E a b,
        ceval M E (CStrBin BConcat (CString a) (CString b)) (CString (a ++ b))

    (* 二元聚合运算 *)

      | E_AggBinAggBMax :
        forall M E a b,
        ceval M E (CAggBin BMax (CInt a) (CInt b)) (CInt (Z.max a b))

      | E_AggBinAggBMax1 :
        forall M E a b,
        ceval M E (CAggBin BMax (CReal a) (CReal b)) (CReal (Rmax a b))

      | E_AggBinAggMin :
        forall M E a b,
        ceval M E (CAggBin BMin (CInt a) (CInt b)) (CInt (Z.min a b))

      | E_AggBinAggMin1 :
        forall M E a b,
        ceval M E (CAggBin BMin (CReal a) (CReal b)) (CReal (Rmin a b))


      | E_AggBinAggBMod :
        forall M E a b,
        ceval M E (CAggBin BMod (CInt a) (CInt b)) (CInt (Z.modulo a b))


      | E_AggBinAggBDivInt :
        forall M E a b,
        ceval M E (CAggBin BDivInt (CInt a) (CInt b)) (CInt (a / b)%Z)


  (*  对象 / 属性 / 角色  *)

      | E_Attr :
        forall M E oid attr,
        ceval M E (CAttr (CObject oid) attr) ((attrs ((objects M) oid)) attr)

      | E_Role :
        forall M E oid role,
        ceval M E (CRole (CObject oid) role) (CObject ((roles ((objects M) oid)) role) )

      | E_NRole :
        forall M E oid nrole,
        ceval M E (CNRole (CObject oid) nrole) (CBagLiteral ((nroles ((objects M) oid)) nrole) )



  (*  集合（Bag） *)



  (*  allInstances  *)

      | E_AllInstances :
        forall M E cname,
        ceval M E (CAllInstances cname) (CBagLiteral ((cmap M) cname) )


  (*  Bag 运算  *)
       *)



  (*  Iterator（绑定变量！）, forall，exists中的varList是语法糖，可脱糖为单变量表示 *)



      | E_CForAll :
        forall M E bag_tm var body vs b,
          ceval M E bag_tm (V_Bag vs) ->
          E_Forall M E var body vs b ->
          ceval M E (CForAll bag_tm var body) (V_Bool b)


      | E_CExists :
          forall M E bag_tm var body vs b,
            ceval M E bag_tm (V_Bag vs) ->
            E_Exists M E var body vs b ->
            ceval M E (CExists bag_tm var body) (V_Bool b)


      | E_CSelect :
          forall M E bag_tm var body vs vs',
            ceval M E bag_tm (V_Bag vs) ->
            E_Select M E var body vs vs' ->
            ceval M E (CSelect bag_tm var body) (V_Bag vs')


      | E_CReject :
          forall M E bag_tm var body vs vs',
            ceval M E bag_tm (V_Bag vs) ->
            E_Reject M E var body vs vs' ->
            ceval M E (CReject bag_tm var body) (V_Bag vs')


      | E_COne :
            forall M E bag_tm var body vs b,
              ceval M E bag_tm (V_Bag vs) ->
              E_One M E var body vs b ->
              ceval M E (COne bag_tm var body) (V_Bool b)



      | E_CCollect :
            forall M E bag_tm attr vs vs',
              ceval M E bag_tm (V_Bag vs) ->
              E_Collect M E attr vs vs' ->
              ceval M E (CCollect bag_tm attr) (V_Bag vs')



      | E_CRCollect :
            forall M E bag_tm role vs vs',
              ceval M E bag_tm (V_Bag vs) ->
              E_RCollect M E role vs vs' ->
              ceval M E (CRCollect bag_tm role) (V_Bag vs')


      | E_CNRCollect :
            forall M E bag_tm nrole vs vs',
              ceval M E bag_tm (V_Bag vs) ->
              E_NRCollect M E nrole vs vs' ->
              ceval M E (CNRCollect bag_tm nrole) (V_Bag vs')

              

      with E_Forall :
            obj_model -> env -> string -> tm ->
            list value -> bool -> Prop :=
      
        | E_ForallNil :
            forall M E var body,
            E_Forall M E var body [] true
        
        | E_ForallConsTrue :
            forall M E var body v tl,
              ceval M (update E var v) body (V_Bool true) ->
              E_Forall M E var body tl true ->
              E_Forall M E var body (v :: tl) true
        
        | E_ForallConsFalse :
            forall M E var body v tl,
              ceval M (update E var v) body (V_Bool false) ->
              E_Forall M E var body (v :: tl) false

      with E_Exists :
            obj_model -> env -> string -> tm ->
            list value -> bool -> Prop :=

        | E_ExistsNil :
            forall M E var body,
              E_Exists M E var body [] false
        
        | E_ExistsConsTrue :
            forall M E var body v tl,
              ceval M (update E var v) body (V_Bool true) ->
              E_Exists M E var body (v :: tl) true
        
        | E_ExistsConsFalse :
            forall M E var body v tl,
              ceval M (update E var v) body (V_Bool false) ->
              E_Exists M E var body tl true ->
              E_Exists M E var body (v :: tl) true

      with E_Select :
          obj_model -> env -> string -> tm ->
          list value -> list value -> Prop :=

        | E_SelectNil :
            forall M E var body,
              E_Select M E var body [] []

        | E_SelectConsKeep :
            forall M E var body v tl out_tl,
              ceval M (update E var v) body (V_Bool true) ->
              E_Select M E var body tl out_tl ->
              E_Select M E var body (v :: tl) (v :: out_tl)

        | E_SelectConsDrop :
            forall M E var body v tl out_tl,
              ceval M (update E var v) body (V_Bool false) ->
              E_Select M E var body tl out_tl ->
              E_Select M E var body (v :: tl) out_tl

      with E_Reject :
              obj_model -> env -> string -> tm ->
              list value -> list value -> Prop :=
        
        | E_RejectNil :
            forall M E var body,
              E_Reject M E var body [] []
        
        | E_RejectConsKeep :
            forall M E var body v tl out_tl,
              ceval M (update E var v) body (V_Bool false) ->
              E_Reject M E var body tl out_tl ->
              E_Reject M E var body (v :: tl) (v :: out_tl)
        
        | E_RejectConsDrop :
            forall M E var body v tl out_tl,
              ceval M (update E var v) body (V_Bool true) ->
              E_Reject M E var body tl out_tl ->
              E_Reject M E var body (v :: tl) out_tl
        

      with E_One :
              obj_model -> env -> string -> tm ->
              list value -> bool -> Prop :=
        
        | E_OneTrue :
            forall M E var body bag res,
              E_Select M E var body bag res ->
              length res = 1 ->
              E_One M E var body bag true
        
        | E_OneFalse :
            forall M E var body bag res,
              E_Select M E var body bag res ->
              length res <> 1 ->
              E_One M E var body bag false


      with E_Attr :
              obj_model -> value -> string -> value -> Prop :=

        | E_ObjAttr :
            forall M oid attr v,
              attrs (objects M oid) attr = v ->
              E_Attr M (V_Object oid) attr v


      with E_Collect :
              obj_model -> env -> string ->
              list value -> list value -> Prop :=
        
        | E_CollectNil :
            forall M E attr,
              E_Collect M E attr [] []
        
        | E_CollectCons :
            forall M E attr v tl v_attr out_tl,
              E_Attr M v attr v_attr ->
              E_Collect M E attr tl out_tl ->
              E_Collect M E attr (v :: tl) (v_attr :: out_tl)
            

      with E_Role :
              obj_model -> value -> string -> value -> Prop :=
        | E_ObjRole :
            forall M oid role r_oid,
              roles (objects M oid) role = r_oid ->
              E_Role M (V_Object oid) role (V_Object r_oid)


      with E_RCollect :
              obj_model -> env -> string ->
              list value -> list value -> Prop :=
        
        | E_RCollectNil :
            forall M E role,
              E_RCollect M E role [] []
        
        | E_RCollectCons :
            forall M E role v tl v' out_tl,
              E_Role M v role v' ->
              E_RCollect M E role tl out_tl ->
              E_RCollect M E role (v :: tl) (v' :: out_tl)



      with E_NRole :
              obj_model -> value -> string -> list value -> Prop :=
        | E_ObjNRole :
            forall M oid role oids,
              nroles (objects M oid) role = oids ->
              E_NRole M (V_Object oid) role (map V_Object oids)


      with E_NRCollect :
              obj_model -> env -> string ->
              list value -> list value -> Prop :=
            
        | E_NRCollectNil :
            forall M E role,
              E_NRCollect M E role [] []
        
        | E_NRCollectCons :
            forall M E role v tl vs out_tl,
              E_NRole M v role vs ->
              E_NRCollect M E role tl out_tl ->
              E_NRCollect M E role (v :: tl) (vs ++ out_tl).

