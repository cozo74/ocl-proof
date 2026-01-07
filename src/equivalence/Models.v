From Stdlib Require Import String ZArith Reals List.
Import ListNotations.

Open Scope string_scope.


(*************************************************************)
(*                    基本符号与类型                         *)
(*************************************************************)

(* 统一使用 string 表示名字 *)
Definition ClassName := string.
Definition AttrName  := string.
Definition RelName   := string.
Definition RoleName  := string.

(*************************************************************)
(*                 UML 中的属性与类型                        *)
(*************************************************************)

(* OCL / UML 中的基础类型（可后续扩展） *)
Inductive BaseTy : Type :=
  | TyBool
  | TyInt
  | TyReal
  | TyString.

(* UML 属性类型：目前仅支持基础类型 *)
Definition AttrTy := BaseTy.

(* UML 中的属性 = 属性名 + 属性类型 *)
Record Attribute : Type := {
  attr_name : AttrName;
  attr_ty   : AttrTy
}.

(*************************************************************)
(*                  UML 中的 Multiplicity                    *)
(*************************************************************)

(* 只允许 1 和 n *)
Inductive Multiplicity : Type :=
  | One     (* 1 *)
  | Many.  (* n *)

(*************************************************************)
(*                       UML 类定义                          *)
(*************************************************************)

(* UML 类 = 类名 + 属性列表 *)
Record UClass : Type := {
  class_name : ClassName;
  class_attrs : list Attribute
}.

(*************************************************************)
(*                     UML 关系定义                          *)
(*************************************************************)

(* UML 关系 / Association *)
Record UAssociation : Type := {
  assoc_name : RelName;

  (* 关系一端 *)
  assoc_c1    : ClassName;
  assoc_role1 : RoleName;
  assoc_mult1 : Multiplicity;

  (* 关系另一端 *)
  assoc_c2    : ClassName;
  assoc_role2 : RoleName;
  assoc_mult2 : Multiplicity
}.

(*************************************************************)
(*                       UML 模型                            *)
(*************************************************************)

(* UML 模型 = 类集合 + 关系集合 *)
Record UMLModel : Type := {
  uml_classes : list UClass;
  uml_assocs  : list UAssociation
}.




Definition assoc_matches_role
  (C : ClassName) (r : RoleName) (a : UAssociation) : bool :=
  (String.eqb a.(assoc_c1) C && String.eqb a.(assoc_role1) r)
  ||
  (String.eqb a.(assoc_c2) C && String.eqb a.(assoc_role2) r).





Fixpoint lookup_role_assoc
  (UA : list UAssociation) (C : ClassName) (r : RoleName)
  : option UAssociation :=
  match UA with
  | [] => None
  | a :: assocs' =>
      if assoc_matches_role C r a
      then Some a
      else
        lookup_role_assoc assocs' C r
  end.







(*************************************************************)
(*                关系数据库 Schema 定义                     *)
(*************************************************************)

(* 数据库列类型 *)
Inductive ColTy : Type :=
  | TBool
  | TInt
  | TReal
  | TString
  | TOid (C : ClassName).   (* 对象标识符，指向类 C *)

(* 数据库列 *)
Record Column : Type := {
  col_name : string;
  col_ty   : ColTy
}.

(* 数据库表 Schema *)
Record TableSchema : Type := {
  table_name : string;
  table_cols : list Column
}.

(* 整个数据库 Schema *)
Definition Schema := list TableSchema.

(*************************************************************)
(*                    命名辅助函数                           *)
(*************************************************************)

(* 将类名转为 oid 列名：类名 + "_id" *)
Definition oidColName (C : ClassName) : string :=
  C ++ "_id".

(* UML 属性类型 → 列类型 *)
Definition mapAttrTy (t : AttrTy) : ColTy :=
  match t with
  | TyBool   => TBool
  | TyInt    => TInt
  | TyReal   => TReal
  | TyString => TString
  end.

(*************************************************************)
(*          UML 类 → 数据库表 的转换规则                     *)
(*************************************************************)

(* 
   转换规则 1：
   每个 UML 类转换为一张表：
   - 表名 = 类名
   - 列：
       * oid 列：<classname>_id
       * 每个属性对应一列
*)
Definition classToTable (C : UClass) : TableSchema :=
  {|
    table_name := C.(class_name);
    table_cols :=
      (* oid 列 *)
      ({|
         col_name := oidColName C.(class_name);
         col_ty   := TOid C.(class_name)
       |}
       ::
       (* 属性列 *)
       map
         (fun a =>
            {|
              col_name := a.(attr_name);
              col_ty   := mapAttrTy a.(attr_ty)
            |})
         C.(class_attrs))
  |}.

(*************************************************************)
(*          UML 关系 → 数据库表 的转换规则                   *)
(*************************************************************)

(*
   转换规则 2：
   每个 UML 关系转换为一张表：
   - 表名 = 关系名
   - 两个列：
       * c1 的 oid 列
       * c2 的 oid 列

   说明：
   - 这里假设 assoc_c1 ≠ assoc_c2（非自关联）
   - 若需要支持自关联，需扩展列命名规则
*)
Definition assocToTable (R : UAssociation) : TableSchema :=
  {|
    table_name := R.(assoc_name);
    table_cols :=
      [
        {|
          col_name := oidColName R.(assoc_c1);
          col_ty   := TOid R.(assoc_c1)
        |};
        {|
          col_name := oidColName R.(assoc_c2);
          col_ty   := TOid R.(assoc_c2)
        |}
      ]
  |}.

(*************************************************************)
(*              UML 模型 → Schema 的整体转换                 *)
(*************************************************************)

Definition umlToSchema (M : UMLModel) : Schema :=
  List.app (map classToTable M.(uml_classes))
  (map assocToTable M.(uml_assocs)).



(* 


(*************************************************************)
(*                     测试用 UML 模型                        *)
(*************************************************************)

(* 类 Person *)
Definition PersonClass : UClass :=
  {|
    class_name := "Person";
    class_attrs :=
      [
        {| attr_name := "name"; attr_ty := TyString |};
        {| attr_name := "age";  attr_ty := TyInt |}
      ]
  |}.

(* 类 Company *)
Definition CompanyClass : UClass :=
  {|
    class_name := "Company";
    class_attrs :=
      [
        {| attr_name := "cname"; attr_ty := TyString |}
      ]
  |}.


(* 关系 WorksFor *)
Definition WorksForAssoc : UAssociation :=
  {|
    assoc_name  := "WorksFor";

    assoc_c1    := "Person";
    assoc_role1 := "employee";
    assoc_mult1 := Many;

    assoc_c2    := "Company";
    assoc_role2 := "employer";
    assoc_mult2 := One
  |}.


(* UML 模型 *)
Definition ExampleModel : UMLModel :=
  {|
    uml_classes := [PersonClass; CompanyClass];
    uml_assocs  := [WorksForAssoc]
  |}.

(*************************************************************)
(*                 测试：生成的 Schema                        *)
(*************************************************************)

(* 这是最终结果，你可以在 Coq 里用 Compute 查看 *)
Compute umlToSchema ExampleModel.
 *)




(*************************************************************)
(*                对象模型（无 null 语义）                   *)
(*************************************************************)

(* 对象标识符 *)
Definition Oid := string.

(* 运行时值 *)
(* Inductive Value : Type :=
| VInt    : Z -> Value
| VReal   : R -> Value
| VBool   : bool -> Value
| VString : string -> Value
| VOid    : Oid -> Value. *)

Inductive value : Type :=
  | V_Bool   : bool -> value
  | V_Int    : Z -> value
  | V_Real   : R -> value
  | V_String : string -> value
  | V_Object    : Oid -> value
  | V_Bag    : list value -> value.



(* 单个对象
   - 所有属性、mandatory role 都是全定义
   - multiplicity=1 / n 在结构上区分 *)
Record Object : Type := {
  obj_class  : ClassName;

  (* 属性：总函数（无 null） *)
  obj_attrs  : AttrName -> value;

  (* multiplicity = 1 的 role *)
  obj_role1  : RoleName -> Oid;

  (* multiplicity = n 的 role *)
  obj_rolen  : RoleName -> list Oid
}.

(* 对象模型
   all_oids 明确给出对象全集，
   避免“任意 nat 都是对象”的不可证明设定 *)
Record ObjectModel : Type := {
  all_oids : list Oid;
  objects  : Oid -> Object
}.


(*************************************************************)
(*                Schema-aware Row                           *)
(*************************************************************)


(* 列名 *)
Definition ColName := string.

(* Row schema = 列名集合 *)
Definition RowSchema := list ColName.


(* 一行：显式携带 schema *)
Record Row : Type := {
  r_schema : RowSchema;

  (* 只对 schema 中的列返回 Value *)
  r_get    : ColName -> option value
}.


(*************************************************************)
(*                数据库实例                                *)
(*************************************************************)

Definition TableInst := list Row.

Record DBInstance : Type := {
  schema : Schema;
  tables : string -> option  TableInst
}.


(*************************************************************)
(*                    enc：总体目标                           *)
(*                                                           *)
(*  将 UML 对象模型（ObjectModel结构性地展开为                *)
(*  符合 UML→Schema 的数据库实例（DBInstance）               *)
(*                                                           *)
(*  设计要点：                                               *)
(*  - 无 null / 无 undefined                                 *)
(*  - Row 显式携带 schema                                    *)
(*  - enc 只依赖 UML 结构，不涉及 RA / OCL 语义              *)
(*************************************************************)

(*************************************************************)
(*  类的属性名列表                                           *)
(*  用于：                                                   *)
(*  - 构造类表 row 的 schema                                 *)
(*  - 后续证明 projection / 属性访问                         *)
(*************************************************************)

Definition classAttrNames (C : UClass) : list AttrName :=
  map attr_name C.(class_attrs).


(*************************************************************)
(*  表名判定函数                                             *)
(*  enc 中唯一使用 find 的地方                               *)
(*************************************************************)

Definition isClassTable
  (M : UMLModel) (tname : string) : option UClass :=
  find (fun C => String.eqb C.(class_name) tname)
       M.(uml_classes).

Definition isAssocTable
  (M : UMLModel) (tname : string) : option UAssociation :=
  find (fun R => String.eqb R.(assoc_name) tname)
       M.(uml_assocs).


(*************************************************************)
(*  类表 row 的 schema                                       *)
(*  = oid 列 + 属性列                                        *)
(*************************************************************)

Definition classRowSchema
  (C : ClassName) (attrs : list AttrName) : RowSchema :=
  oidColName C :: attrs.


(*************************************************************)
(*  类表中的一行                                             *)
(*  - oid 列：对象 id                                        *)
(*  - 属性列：来自对象属性                                  *)
(*                                                           *)
(*  注意：                                                   *)
(*  - r_schema 精确等于 UML→Schema 的类表 schema             *)
(*  - r_get 只在 schema 列上返回 Some                        *)
(*************************************************************)

Definition classRow
  (o     : Oid)
  (obj   : Object)
  (attrs : list AttrName)
  : Row :=
  {|
    r_schema := classRowSchema obj.(obj_class) attrs;

    r_get :=
      fun col =>
        if String.eqb col (oidColName obj.(obj_class)) then
          Some (V_Object o)
        else if in_dec string_dec col attrs then
          Some (obj.(obj_attrs) col)
        else
          None
  |}.

(*************************************************************)
(*  关系表 row 的 schema                                     *)
(*  = [c1_id ; c2_id]                                        *)
(*************************************************************)

Definition assocRowSchema
  (c1 c2 : ClassName) : RowSchema :=
  [ oidColName c1; oidColName c2 ].


(*************************************************************)
(*  关系表中的一行                                           *)
(*  表示一条关联边 (o1 , o2)                                 *)
(*************************************************************)

Definition assocRow
  (c1 c2 : ClassName)
  (o1 o2 : Oid)
  : Row :=
  {|
    r_schema := assocRowSchema c1 c2;

    r_get :=
      fun col =>
        if String.eqb col (oidColName c1) then
          Some (V_Object o1)
        else if String.eqb col (oidColName c2) then
          Some (V_Object o2)
        else
          None
  |}.



(*************************************************************)
(*  encClassTable                                            *)
(*                                                           *)
(*  对于一个 UML 类 C：                                      *)
(*  - 遍历 all_oids                                          *)
(*  - 选出 obj_class = C 的对象                              *)
(*  - 为每个对象生成一行 classRow                            *)
(*************************************************************)

Definition encClassTable
  (C  : UClass)
  (OM : ObjectModel)
  : TableInst :=
  let attrs := classAttrNames C in
  map
    (fun o =>
       let obj := OM.(objects) o in
       classRow o obj attrs)
    (filter
       (fun o =>
          String.eqb (OM.(objects) o).(obj_class)
                     C.(class_name))
       OM.(all_oids)).



(*************************************************************)
(*  encAssocTable                                            *)
(*                                                           *)
(*  对于一个 UML 关系 R：                                    *)
(*  - 仅遍历源类 assoc_c1 的对象作为源对象 o1               *)
(*  - 对每个源对象 o1，根据 assoc_mult1 决定关联方式        *)
(*    · multiplicity = One ：                                *)
(*        使用 obj_role1 assoc_role1                         *)
(*        生成恰好一条 (o1, o2) 的关系行                     *)
(*    · multiplicity = Many：                                *)
(*        使用 obj_rolen assoc_role1                         *)
(*        对每个目标对象 o2 生成一条关系行                  *)
(*                                                           *)
(*  enc 不检查 multiplicity 与对象模型的一致性，             *)
(*  假设 UML 模型与对象模型是 well-formed                    *)
(*************************************************************)


Definition encAssocTable
  (R  : UAssociation)
  (OM : ObjectModel)
  : TableInst :=
  concat
    (map
       (fun o1 =>
          let obj1 := OM.(objects) o1 in
          match R.(assoc_mult1) with
          | One =>
              (* multiplicity = 1：恰好一个目标对象 *)
              let o2 := obj1.(obj_role1) R.(assoc_role1) in
              [ assocRow
                  R.(assoc_c1)
                  R.(assoc_c2)
                  o1 o2 ]

          | Many =>
              (* multiplicity = n：多个目标对象 *)
              map
                (fun o2 =>
                   assocRow
                     R.(assoc_c1)
                     R.(assoc_c2)
                     o1 o2)
                (obj1.(obj_rolen) R.(assoc_role1))
          end)
       (* 只遍历源类 assoc_c1 的对象 *)
       (filter
          (fun o1 =>
             String.eqb (OM.(objects) o1).(obj_class)
                        R.(assoc_c1))
          OM.(all_oids))).




(*************************************************************)
(*  enc：对象模型 → 数据库实例                               *)
(*                                                           *)
(*  表名分三种情况：                                         *)
(*  1. 类表名 → encClassTable                                *)
(*  2. 关系表名 → encAssocTable                              *)
(*  3. 其它名字 → 空表                                       *)
(*************************************************************)

Definition enc
  (M  : UMLModel)
  (OM : ObjectModel)
  : DBInstance :=
  {|
    schema := umlToSchema M;
    tables :=
      fun tname =>
        match isClassTable M tname with
        | Some C =>
            Some (encClassTable C OM)
        | None =>
            match isAssocTable M tname with
            | Some R =>
                Some (encAssocTable R OM)
            | None =>
                None
            end
        end
  |}.
