
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



Record obj := {
  oid   : string;             (* object identity *)
  cname  : class;              (* object's class name *)
  attrs : total_map tm;   (* attribute map *)
  roles : total_map string;  (* association role -> list of target object IDs *)
  nroles : total_map (list tm);  (* association role -> list of target object IDs *)
}.

Record obj_model := {
  objects : total_map obj;   (* object id -> object *)
  cmap : total_map (list tm);
}.


Definition objects_of_class (M : obj_model) (C : string) : list tm :=
  cmap M C.



Definition env := total_map tm.     (* var name -> term *)


Inductive value : tm -> Prop :=
    | v_true : value (CBool true)
    | v_false : value (CBool false).




Inductive step : obj_model -> env -> tm -> tm -> Prop :=

      (* context C inv body 语义：对所有实例执行 forAll *)
      | E_Context_tru :
          forall M E C body,
          E_Forall M E "self" body ((cmap M) C) (CBool true) ->
            step M E (CContext C body) (CBool true)
      
      | E_Context_fls :
          forall M E C body,
          E_Forall M E "self" body ((cmap M) C) (CBool false) ->
            step M E (CContext C body) (CBool false)
      

      | E_Var :
          forall M E var,
          step M E (CVar var) (E var)

      | E_Self :
          forall M E,
          step M E CSelf (E "self")

      
      | E_BoolUnUNotTru :
        forall M E,
        step M E (CBoolUn UNot (CBool true)) (CBool false )


      | E_BoolUnUNotFls :
        forall M E,
        step M E (CBoolUn UNot (CBool false)) (CBool true)


      | E_ArithUnIntUNeg :
        forall M E n,
        step M E (CArithUn UNeg (CInt n)) ( CInt (-n))

      | E_ArithUnIntUAbs :
        forall M E n,
        step M E (CArithUn UAbs (CInt n)) ( CInt (Z.abs n))


      | E_ArithUnRealUNeg :
        forall M E r,
        step M E (CArithUn UNeg (CReal r)) ( CReal (-r))

      | E_ArithUnRealUAbs :
        forall M E r,
        step M E (CArithUn UAbs (CReal r)) ( CReal (Rabs r))

      | E_ArithUnRealUFloor :
        forall M E r z,
        Rfloor_real r z ->
        step M E (CArithUn UFloor (CReal r)) ( CInt z)

      | E_ArithUnRealURound :
        forall M E r z,
        Rround_real r z ->
        step M E (CArithUn URound (CReal r)) ( CInt z)


      | E_StrUnUToUpper :
        forall M E s,
        step M E (CStrUn UToUpper (CString s)) ( CString (toUpper s) )

      | E_StrUnUToLower :
        forall M E s,
        step M E (CStrUn UToLower (CString s)) ( CString (toLower s) )




      with E_Forall :
            obj_model -> env -> string -> tm ->
            list tm -> tm -> Prop :=
      
      | E_ForallNil :
          forall M E var body,
          E_Forall M E var body [] (CBool true)
      
      | E_ForallConsTrue :
          forall M E var body hd tl,
            step M (update E var hd) body (CBool true) ->
            E_Forall M E var body tl (CBool true) ->
            E_Forall M E var body (hd :: tl) (CBool true)
      
      | E_ForallConsFalse :
          forall M E var body hd tl,
            step M (update E var hd) body (CBool false) ->
            E_Forall M E var body (hd :: tl) (CBool false)

      with E_Exists :
            obj_model -> env -> string -> tm ->
            list tm -> tm -> Prop :=
      
        | E_Exists_True :
            forall M E bag var body,
              (* exists = not (forall x in bag | not body) *)
              E_Forall M E var (CBoolUn UNot body) bag (CBool false) ->
              E_Exists M E var body bag (CBool true)
        
        | E_Exists_False :
            forall M E bag var body,
            E_Forall M E var (CBoolUn UNot body) bag (CBool true) ->
              E_Exists M E var body bag (CBool false)
      with E_Select :  (* select x in bag | body *)
            obj_model -> env -> string -> tm -> list tm -> list tm -> Prop :=
        
            | E_SelectNil :
              forall M E var body,
              E_Select M E var body [] []

            (* head 满足 body → 保留 head *)
            | E_SelectConsKeep :
                forall M E var body hd tl out_tl,
                  step M (update E var hd) body (CBool true) ->
                  E_Select M E var body tl out_tl ->
                  E_Select M E var body (hd :: tl) (hd :: out_tl)

            (* head 不满足 body → 丢弃 head *)
            | E_SelectConsDrop :
                forall M E var body hd tl out_tl,
                  step M (update E var hd) body (CBool false) ->
                  E_Select M E var body tl out_tl ->
                  E_Select M E var body (hd :: tl) out_tl

      with E_Reject :  (* reject x in bag | body *)
            obj_model -> env -> string -> tm -> list tm -> list tm -> Prop :=
        
        | SRejectNil :
          forall M E var body,
          E_Reject M E var body [] []
            
        | E_RejectConsKeep :
            forall M E var body hd tl out_tl,
              step M (update E var hd) body (CBool false) ->
              E_Reject M E var body tl out_tl ->
              E_Reject M E var body (hd :: tl) (hd :: out_tl)
            
        | E_RejectConsDrop :
            forall M E var body hd tl out_tl,
              step M (update E var hd) body (CBool true) ->
              E_Reject M E var body tl out_tl ->
              E_Reject M E var body (hd :: tl) out_tl

      with E_One :  (* one x in bag | body *)
            obj_model -> env -> string -> tm -> list tm -> tm -> Prop :=
        
          
        | E_OneConsTrue :
            forall M E var body bag res,
            E_Select M E var body bag res ->
            length res = 1 ->
            E_One M E var body bag (CBool true)
        
        | E_OneConsFalse :
            forall M E var body bag res,
            E_Select M E var body bag res ->
            length res <> 1 ->
            E_One M E var body bag (CBool false)

      with E_Collect :
            obj_model -> env -> string -> list tm -> list tm -> Prop :=
        
        | E_CollectNil :
            forall M E attr,
            E_Collect M E attr [] []
          
        | E_CollectCons :
            forall M E attr hd tl out_hd out_tl,
            step M E (CAttr hd attr) out_hd ->
            E_Collect M E attr tl out_tl ->
            E_Collect M E attr (hd :: tl) (out_hd :: out_tl)

      with E_RCollect :
            obj_model -> env -> string -> list tm -> list tm -> Prop :=
          
        | E_RCollectNil :
            forall M E role,
            E_RCollect M E role [] []
          
        | E_RCollectCons :
            forall M E role hd tl out_hd out_tl,
            step M E (CRole hd role) out_hd ->
            E_RCollect M E role tl out_tl ->
            E_RCollect M E role (hd :: tl) (out_hd :: out_tl)

      with E_NRCollect :
            obj_model -> env -> string -> list tm -> list tm -> Prop :=
          
        | E_NRCollectNil :
            forall M E role,
            E_NRCollect M E role [] []
          
        | E_NRCollectCons :
            forall M E role hd tl out_hd out_tl,
            step M E (CNRole hd role) out_hd ->
            E_NRCollect M E role tl out_tl ->
            E_NRCollect M E role (hd :: tl) (out_hd :: out_tl).

