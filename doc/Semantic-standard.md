





## A.1 Object Models





### A.1.1 Syntax of Object Models

Such a model has the following components:
• a set of classes
• a set of attributes for each class
• a set of associations with role names and multiplicities



For naming model components, we assume in this sub clause an alphabet $A$ and a set of finite, non-empty names $N \subseteq A^+$ over alphabet $A$ to be given, where $A^{+} = \bigcup_{n=1}^{\infty} A^{n}$.



#### A.1.1.1 Types

For now, we assume that there is a signature with $\Sigma=(\mathcal{T}, \Omega)$ being a
set of type names, and $\Omega$ being a set of operations over types in $\mathcal{T}$.



#### A.1.1.2 Classes

The central concept of UML for modeling entities of the problem domain is the class. A class provides a common description for a set of objects sharing the same properties.


> **Definition A.1 (Classes)**
> The set of classes is a finite set of names $CLASS \subseteq N$.

Each class $c \in CLASS$ induces an object type $t_c \in \mathcal{T}$ having the same name as the class. A value of an object type refers to an object of the corresponding class. The main difference between classes and object types is that the interpretation of the latter includes a special undefined value and a special invalid value.

#### A.1.1.3 Attributes

Attributes are part of a class declaration in UML. Objects are associated with attribute values describing properties of the object. An attribute has a name and a type specifying the domain of attribute values.


> **Definition A.2 (Attributes)**
> Let $t \in T$ be a type. The attributes of a class $c \in CLASS$ are defined as a set $ATT_c$ of signatures $a:t_c \rightarrow t$ where the attribute name $a$ is an element of $N$, and $t_c \in T$ is the type of class $c$.


All attributes of a class have distinct names. In particular, an attribute name may not be used again to define another attribute with a different type.
$ \forall t, t' \in T: (a: t_c \rightarrow t \in ATT_c \ and \ a:t_c \rightarrow t' \in ATT_c) \Rightarrow t=t'$

#### A.1.1.5 Associations
Associations describe structural relationships between classes. Generally, classes may participate in any number of associations, and associations connect two classes. 

> **Definition A.4 (Associations)**
> The set of associations is given by
> i. a finite set of names $ASSOC \in N$,
> ii. a function associates: $$
\begin{cases}
ASSOC \rightarrow CLASS^+ \\
as \rightarrow \langle c_1,c_2 \rangle
\end{cases}
$$


The function associates maps each association name $as \in ASSOC$ to a two elements list $\langle c_1, c_2 \rangle$ of classes participating in
the association. The number n of participating classes is also called the degree of an association; associations with degree n are called n-ary associations.For many problems the use of binary associations is often sufficient.

A self-association (or recursive association) $sa$ is a binary association where both ends of the association are attached to the same class $c$ such that associates $(sa) = \langle c, c \rangle$. The function associates does not have to be injective. Multiple associations over the same set of classes are possible. 


##### Role Names

We assign each class participating in an association a unique role name.

> **Definition A.5 (Role Names)**
> Let $as \in ASSOC$ be an association with associates(as) = $\langle c_1, c_2 \rangle$. Role names for an association are defined by a function
> $$
roles :
\begin{cases}
ASSOC \rightarrow N^+ \\
as \rightarrow \langle r_1,r_2 \rangle
\end{cases}
$$
> where all role names must be distinct, i.e., $r_1 \ne r_2$.

Additional syntactical constraints are required for ensuring the uniqueness of role names when a class is part of many associations. We first define a function participating that gives the set of associations a class participates in.

$$
participating :
\begin{cases}
CLASS \rightarrow P(ASSOC) \\
c \rightarrow \{ as | as \in ASSOC \land associates(as)= \langle c_1, c_2 \rangle \land \exist i \in \{1,2\} : c_i=c \}
\end{cases}
$$

The following function navends gives the set of all role names reachable (or navigable) from a class over a given association.

$$
navends :
\begin{cases}
CLASS \times ASSOC  \rightarrow P(N) \\
(c,as) \rightarrow \{r|associates(as) = \langle c_1, c_2 \rangle
\land roles(as) = \langle r_1, r_2 \rangle  \land \exist i,j \in \{1,2\} : (i \ne j \land c_i=c \land r_j=r) \}
\end{cases}
$$

The set of role names that are reachable from a class along all associations the class participates in can then be determined by the following function.

$$
navends(c) :
\begin{cases}
CLASS \rightarrow P(N) \\
c \rightarrow \bigcup_{as \in participating(c)} navends(c, as)
\end{cases}
$$





##### Multiplicities

An association specifies the possible existence of links between objects of associated classes. The number of links that an object can be part of is specified with multiplicities. A multiplicity specification in UML can be represented by a set of natural numbers.

> **Definition A.6 (Multiplicities)**
> Let $as \in ASSOC$ be an association with associates(as) = $\langle c_1, c_2\rangle$. The function multiplicities(as) = $\langle M_1, M_2\rangle$ assigns each class $c_i$ participating in the association a non-empty set $M_i \subseteq N$ for all $1 \le i \le 2$.


##### Full Descriptor of a Class

> **Definition A.8 (Full Descriptor of a Class)**
> The full descriptor of a class $c \in CLASS$ is a structure $FD_c = (ATT_c, navends(c))$ containing all attributes and navigable role names defined for the class.


The UML standard requires that properties of a full descriptor must be distinct. These constraints are captured more precisely by the following well-formedness rules in our framework. Each constraint must hold for each class $c \in CLASS$.


1. Attribute names and role names must not conflict. This is necessary because in OCL the same notation is used for attribute access and navigation by role name. For example, the expression self.x may either be a reference to an attribute x or a reference to a role name x.

$$\forall (a:t_c \rightarrow t \in ATT_c) : \forall r \in navends(c) :: (a \ne r) $$


#### A.1.1.7 Formal Syntax

We combine the components introduced in the previous sub clause to formally define the syntax of object models.

> **Definition A.9 (Syntax of Object Models)**
> The syntax of an object model is a structure.
$$ M =(CLASS, ATT_c, ASSOC, associates, roles, multiplicities) $$
> where
> i. $CLASS$ is a set of classes (Definition A.1).
> ii. $ATT_c$ is a set of operation signatures for functions mapping an object of class $c$ to an associated attribute value (Definition A.2).
iii. ASSOC is a set of association names (Definition A.4).
    a. associates is a function mapping each association name to a list of participating classes (Definition A.4).
    b. roles is a function assigning each end of an association a role name (Definition A.5).
    c. multiplicities is a function assigning each end of an association a multiplicity specification (Definition A.6).



### A.1.2 Interpretation of Object Models


#### A.1.2.1 Objects

The domain of a class $c \in CLASS$ is the set of objects that can be created by this class and all of its child classes. Objects are referred to by unique object identifiers. In the following, we will make no conceptual distinction between objects and their identifiers. Each object is uniquely determined by its identifier and vice versa. Therefore, the actual representation of an object is not important for our purposes.

> **Definition A.10 (Object Identifiers)**
> i. The set of object identifiers of a class $c \in CLASS$ is defined by an infinite set oid($c$) = $\{ c_1 , c_2, ...\}$
> ii. The domain of a class $c \in CLASS$ is defined as $I_{CLASS}(c) = oid(c)$

In the following, we will omit the index for a mapping I when the context is obvious. The concrete scheme for naming objects is not important as long as every object can be uniquely identified, i.e., there are no different objects having the same name. We sometimes use single letters combined with increasing indexes to name objects if it is clear from the context to which class these objects belong.

#### A.1.2.3 Links

> **Definition A.11 (Links)**
> Each association $as \in ASSOC$ with associates(as) = $ \langle c_1, c_2 \rangle $ is interpreted as the Cartesian product of the sets of object identifiers of the participating classes: $I_{ASSOC}(as) = I_{CLASS}(c_1) \times I_{CLASS}(c_2)$. A link denoting a connection between objects is an element $las \in I_{ASSOC}(as).$








#### A.1.2.4 System State

Objects, links, and attribute values constitute the state of a system at a particular moment in time. A system is in different states as it changes over time. Therefore, a system state is also called a snapshot of a running system. With respect to OCL, we can in many cases concentrate on a single system state given at a discrete point in time. For example, a system state provides the complete context for the evaluation of OCL invariants. For pre- and postconditions, however, it is necessary to consider two consecutive states.


> **Definition A.12 (System State)**
> A system state for a model $M$ is a structure $\sigma(M) = (\sigma_{CLASS}, \sigma_{ATT}, \sigma_{ASSOC})$.
> i. The finite sets $\sigma_{CLASS}(c)$ contain all objects of a class $c \in CLASS$ existing in the system state:
$\sigma_{CLASS}(c) \subset oid(c)$.
> ii. Functions $\sigma_{ATT}$ assign attribute values to each object: $\sigma_{ATT}(a) : \sigma_{CLASS}(c) \rightarrow I(t)$ for each $a:t_c \rightarrow t \in ATT_c$ . (where $I(t)$ denotes value domain of type $t$.)
> iii. The finite sets $\sigma_{ASSOC}$ contain links connecting objects. For each $as \in ASSOC: \sigma_{ASSOC}(as) \subset I_{ASSOC}(as)$. A link set must satisfy all multiplicity specifications defined for an association (the function $\pi_i(l)$ projects the $i$th component of a tuple or list $l$, whereas the function $\overline{\pi}_i(l)$ projects all but the $i$th component):
$$\forall i \in \{1,2 \}, \forall l \in \sigma_{ASSOC}(as) : \big| \{l' | l' \in \sigma_{ASSOC}(as) \land (\overline{\pi}_i(l') = \overline{\pi}_i(l)) \} \big| \in \pi_i(multiplicities(as)) $$


## A.2 OCL Types and Operations

Our general approach to defining the type system is as follows. Types are associated with a set of operations. These operations describe functions combining or operating on values of the type domains. In our approach, we use a data signature $\Sigma = (T, \Omega)$ to describe the syntax of types and operations. The semantics of types in $T$ and operations in $\Omega$ is defined by a mapping that assigns each type a domain and each operation a function.


#### A.2.1 Basic Types

Basic types are Integer, Real, Boolean, and String. The syntax of basic types and their operations is defined by a signature $\Sigma_B = (T_B, \Omega_B)$. $T_B$ is the set of basic types, $\Omega_B$ is the set of signatures describing operations over basic types.


> **Definition A.13 (Syntax Of Basic Types)**
> The set of basic types $T_B$ is defined as $T_B = {Integer, Real, Boolean, String}$. Next we define the
semantics of basic types by mapping each type to a domain.

> **Definition A.14 (Semantics Of Basic Types)**
> Let $A^*$ be the set of finite sequences of characters from a finite alphabet $A$ . The semantics of a basic type $t \in T_B$ is a function $I$ mapping each type to a set:
• $I(Integer) = \mathbb{Z} $
• $I(Real) = \mathbb{R}$
• $I(Boolean) = \{ true, false\}$
• $I(String) = A^*$.
<!-- • $I(OclInvalid) = \{ \bot \} $
• $I(OclVoid) = \{\epsilon,\bot \}$
• $I(Integer) = ℤ \cup \{\epsilon, \bot \}$
• $I(Real) = ℝ \cup \{\epsilon, \bot\}$
• $I(Boolean) = \{ true, false\} \cup \{\epsilon,\bot\}$
• $I(String) = A^* \cup \{\epsilon, \bot \}$
• $I(UnlimitedNatural) = ℕ \cup \{\infty,\epsilon, \bot \}$. -->
<!-- The basic type UnlimitedNatural represents the set of non-negative integers, Integer represents the set of integers, Real the set of real numbers, Boolean the truth values true and false, and String all finite strings over a given alphabet. Each domain also contains two special values $\epsilon$ and $\bot$. $\epsilon$ coresponds to the null value, and $\bot$, pronounced bottom, corresponds to the invalid value. These are motivated in the next sub clause. The UnlimitedNatural domain also includes a special value to denote the unlimited natural number. -->

##### A.2.1.2 Operations

There are a number of predefined operations on basic types. The set $\Omega_B$ contains the signatures of these operations. An operation signature describes the name, the parameter types, and the result type of an operation.

> **Definition A.15 (Syntax Of Operations)**
> The syntax of an operation is defined by a signature $\omega :t_1 \times \cdot \cdot \cdot \times t_n \rightarrow t $. The signature contains the operation symbol $\omega$, a list of parameter types $ t_1, \dots, tn \in T$, and a result type $t \in T$.



Table A.1 shows a schema defining most predefined operations over basic types. The left column contains partially parameterized signatures in $\Omega_B$ . The right column specifies variations for the operation symbols or types in the left column.


The set of predefined operations includes the usual arithmetic operations +, - , _ , /, etc. for integers and real numbers, division (div) and modulo (mod) of integers, sign manipulation ( - , abs), conversion of Real values to Integer values (floor, round), and comparison operations (<, >, < , > ).


Operations for equality and inequality are presented later in sub clause A.2.2, since they apply to all types. Boolean values can be combined in different ways (and, or, xor, implies), and they can be negated (not). For strings the length of a string (size) can be determined, a string can be projected to a substring, and two strings can be concatenated (concat). Finally, assuming a standard alphabet like ASCII or Unicode, case translations are possible with toUpperCase and toLowerCase.

Some operation symbols (such as + and -) are overloaded, that is there are signatures having the same operation symbol but different parameters (concerning number or type) and possibly different result types. Thus in general, the full argument list has to be considered in order to identify a signature unambiguously.

The operations in Table A.1 all have at least one parameter. There is another set of operations in $\Omega_B$ that do not have parameters. These operations are used to produce constant values of basic types. For example, the integer value 12 can be generated by the operation $12 : \rightarrow Integer$. Similar operations exist for the other basic types. For each value, there is an operation with no parameters and an operation symbol that corresponds to the common notational representation of this value.

**Table A.1 - - Schema for operations on basic types**
|               | Signature                                                               | Schema parameters                                                               |
| ------------- | ----------------------------------------------------------------------- | ------------------------------------------------------------------------------- |
| $\omega $:    | $Integer \times Integer \rightarrow Integer$                            | $ \omega \in \{+,-,*,max, min, div, mod\}$                                      |
| $\omega $:    | $Real \times t \rightarrow Real$ <br>  $t \times Real \rightarrow Real$ | $ \omega \in \{+,-,*,max, min\}$ <br>  $t \in \{ Integer, Real\}$               |
| $/ $:         | $t_1 \times t_2 \rightarrow Real$                                       | $ t1, t2 \in \{ Integer, Real\} $                                               |
| $\omega $:    | $t \rightarrow t$                                                       | $ \omega \in \{-, abs\}$ <br> $ t \in \{ Integer, Real\} $                      |
| $\omega $:    | $t \rightarrow Integer$                                                 | $ \omega \in \{floor, round\}$ <br> $ t \in \{ Integer, Real\} $                |
| $\omega $:    | $t_1 \times t_2 \rightarrow Boolean$                                    | $ \omega \in \{\lt, \gt, \le, \ge \}$ <br> $ t \in \{ Integer, Real, String\} $ |
| $\omega $:    | $Boolean \times Boolean \rightarrow Boolean$                            | $ \omega \in \{and, or, xor, implies \}$                                        |
| $not $:       | $Boolean \rightarrow Boolean$                                           |                                                                                 |
| $size $:      | $String \rightarrow Integer$                                            |                                                                                 |
| $concat $:    | $String \times String \rightarrow String$                               |                                                                                 |
| $\omega$:     | $String \rightarrow String$                                             | $\omega \in \{ toUpperCase, toLowerCase \}  $                                   |
| $substring $: | $String \times Integer \times Integer \rightarrow String$               |                                                                                 |
| $toString $:  | $t \rightarrow String$                                                  | $t \in \{Integer, Real, String, Boolean \} $                                    |


##### A.2.1.3 Semantics of Operations
> **Definition A.16 (Semantics of Operations)**
> The semantics of an operation with signature $\omega : t_1 \times \cdot \cdot \cdot \times t_n \rightarrow t $ is a total function $I(\omega: t_1 times \cdot \cdot \cdot \times t_n \rightarrow t) : I(t_1) \times \cdot \cdot \cdot \times I(t_n) \rightarrow I(t)$.

The next example shows the interpretation of the operation + for adding two integers. The operation has two arguments
$i_1, i_2 \in I(Integer)$. This example also demonstrates the strict evaluation semantics for undefined arguments.

$$ I(+)(i_1, i_2) = i_1 + i_2 $$

We can define the semantics of the other operations in Table A.1 analogously. Table A.2 shows the interpretation of Boolean operations. Since the semantics of the other basic operations for UnlimitedNatural, Integer, Real, and String values is rather obvious, we will not further elaborate on them here.

**Table A.2 - - Semantics of Boolean operations**
| $b_1$ | $b_2$ | $b_1 and b_2$ | $b_1 or b_2$ | $b_1 xor b_2$ | $b_1 implies b_2$ | $not b_1$ |
| ----- | ----- | ------------- | ------------ | ------------- | ----------------- | --------- |
| false | false | false         | false        | false         | true              | true      |
| false | true  | false         | true         | true          | true              | true      |
| true  | false | false         | true         | true          | false             | false     |
| true  | true  | true          | true         | false         | true              | false     |


#### A.2.2 Common Operations On All Types


At this point, we introduce some operations that are defined on all types (including those that are defined in subsequent sub clauses). The equality of values of the same type can be checked with the operation $=_t: t \times t \rightarrow Boolean$. Furthermore, the semantics of $=_t$ is defined to be strict. For two values $v_1, v_2 \in I(t)$, we have


$$
 I(=_t)(v_1,v_2)=
\begin{cases}
true \qquad if \ v_1=v_2 \ and \ v_1 \ne \bot \ and \ v_2 \ne \bot \\
\bot \qquad if \ v_1=\bot \ or \ v_2=\bot \\
false \qquad otherwise
\end{cases}
$$

A test for inequality $\ne_t: t \times t \rightarrow Boolean$ can be defined analogously.


#### A.2.4 Object Types

A central part of a UML model are classes that describe the structure of objects in a system. For each class, we define a corresponding object type describing the set of possible object instances. The syntax of object types and their operations is defined by a signature $\Sigma_C = (T_C, \Omega_C)$. $T_C$ is the set of object types, and $\Omega_C$ is the set of signatures describing operations on object types.


> **Definition A.19 (Syntax Of Object Types)**
> Let $M$ be a model with a set CLASS of class names. The set $T_C$ of object types is defined such that for each class $c \in CLASS$ there is a type $t \in T_C$ having the same name as the class $c$.

We define the following two functions for mapping a class to its type and vice versa.

$typeOf : CLASS \rightarrow T_C$
$classOf : T_C \rightarrow CLASS$

The interpretation of classes is used for defining the semantics of object types. The set of object identifiers $I_{CLASS}(c)$ was introduced in "Definition A.10 (Object Identifiers)".



> **Definition A.20 (Semantics Of Object Types)**
> The semantics of an object type $t \in T_C$ with $classOf(t) = c$ is defined as $I(t) = I_{CLASS}(c)$.

In summary, the domain of an object type is the set of object identifiers defined for the class.

##### A.2.4.1 Operations

There are three different kinds of operations that are specific to object types:
1. Predefined operations: These are operations that are implicitly defined in OCL for all object types.
2. Attribute operations: An attribute operation allows access to the attribute value of an object in a given system state.

3. Navigation operations: An object may be connected to other objects via association links. A navigation expression allows one to follow these links and to retrieve connected objects.


##### A.2.4.2 Predefined Operations

For all classes $c \in CLASS$ with object type $t_c = typeOf(c)$ the operations

$allInstances_{t_c} : \rightarrow Set(t_c)$

are in $\Omega_C$ . The semantics is defined as

$I(allInstances_{t_c} : \rightarrow Set(t_c)) = \sigma_{CLASS}(c).$

This interpretation of allInstances is safe in the sense that its result is always limited to a finite set. The extension of a class is always a finite set of objects.


##### A.2.4.3 Attribute Operations

Attribute operations are declared in a model specification by the set $ATT_c$ for each class $c$. The set contains signatures $a : t_c \rightarrow t$ with a being the name of an attribute defined in the class $c$. The type of the attribute is $t$. All attribute operations in $ATT_c$ are elements of $\Omega_C$. The semantics of an attribute operation is a function mapping an object identifier to a value of the attribute domain. An attribute value depends on the current system state.


> **Definition A.21 (Semantics of Attribute Operations)**
> An attribute signature $a : t_c \rightarrow t$ in $\Omega_C$ is interpreted by an attribute value function $I_{ATT}(a : t_c \rightarrow t) : I(t_c) \rightarrow I(t)$ mapping objects of class $c$ to a value of type $t$.
$$
I_{ATT}(a : t_c \rightarrow t)(\underline{c})
\begin{cases}
\Omega_{ATT}(a)(\underline{c}) \qquad if \ c \in \Omega_{CLASS}(c) \\
\bot \qquad otherwise \\
\end{cases}
$$

Note that attribute functions are defined for all possible objects. The attempt to access an attribute of a non-existent object results in the invalid value.


#### A.2.4.5 Navigation Operations

> **Definition A.22 (Syntax of Navigation Operations)**
> Let M be a model
$$ M =(CLASS, ATT_c, ASSOC, associates, roles, multiplicities) $$
> The set $\Omega_{nav}(c)$ of navigation operations for a class $ c \in CLASS$ is defined such that for each association $as \in participating(c)$ with $associates(as) = \langle c_1, c_2 \rangle$, $roles(as) = \langle r_1, r_2 \rangle$, and $multiplicities(as) = \langle M_1, M_2 \rangle$ the following signatures are in $\Omega_{nav}(c)$.
> For all $i, j \in \{1, 2\}$ with $i \ne j$, $c_i = c$, $t_{c_i} = typeOf(c_i)$, and $t_{c_j} = typeOf(c_j)$
> i. $if \ M_j - \{0, 1\} = \emptyset  \ then \  r_{j(as;r_i)} : t_{c_i} \rightarrow t_{c_j} \in \Omega_{nav}(c) $.
> ii. $if \ M_j - \{0, 1\} \ne \emptyset  \ then \  r_{j(as;r_i)} : t_{c_i} \rightarrow Set(t_{c_j}) \in \Omega_{nav}(c) $.


We use unique role names instead of class names for navigation operations in order to avoid ambiguities. The result type of a navigation over binary associations is the type of the target class if the multiplicity of the target is given as 0..1 or 1 (i). All other multiplicities allow an object of the source class to be linked with multiple objects of the target class. Therefore, we need a set type to represent the navigation result.


> **Definition A.23 (Semantics of Navigation Operations)**
> The set of objects of class $c_j$ linked to an object $c_i$ via association $as$ is defined as
> $$ L(as)(\underline{c}_i) = \{ \underline{c}_j | (\underline{c}_1, ..., \underline{c}_i,...,\underline{c}_j,...,\underline{c}_n ) \in \sigma_{ASSOC}(as) \} $$
> The semantics of operations in $\Omega_{nav}(c)$ is then defined as
i. $
I(t_{j(as,ri)}:t_{c_i} \rightarrow t_{c_j}(\underline{c}_i)= )
\begin{cases}
(\underline{c}_j) \quad if \ \underline{c}_j \in L(as)(\underline{c}_i), \\
\bot \qquad otherwise
\end{cases}
$
ii. $ I(t_{j(as,ri)}:t_{c_i} \rightarrow Set(t_{c_j}))(\underline{c}_i) = L(as)(\underline{c}_i) $.


#### A.2.5 Collection and Tuple Types

We call a type that allows the aggregation of several values into a single value a complex type. OCL provides the complex types $Set(t)$, $Sequence(t)$, and $Bag(t)$ for describing collections of values of type $t$. There is also a supertype $Collection(t)$ that describes common properties of these types. The OCL collection types are homogeneous in the sense that all elements of a collection must be of the same type $t$.



A.2.5.1 Syntax and Semantics

> **Definition A.24 (Type Expressions)**
> Let $\hat{T}$ be a set of types and $l_1, \cdot \cdot \cdot , l_n \in N$ a set of disjoint names. The set of type expressions $T_{Expr}(\hat{T})$ over $\hat{T}$ is defined as follows.
i. If $t \in \hat{T}$ then $ t\in T_{Expr}( \hat{T})$.
ii. if $t \in T_{Expr}$ then $Set(t), Bag(t) \in T_{Expr}(\hat{T}) $.


The definition says that every type $t \in \hat{T}$ can be used as an element type for constructing a set, sequence, bag, or collection type. The components of a tuple type are marked with labels $l_1, \cdot \cdot \cdot , l_n$. Complex types may again be used as element types for constructing other complex types. The recursive definition allows unlimited nesting of type expressions.


For the definition of the semantics of type expressions we make the following conventions. Let $F(S)$ denote the set of all finite subsets of a given set $S$, $S^*$ is the set of all finite sequences over $S$, and $B(S)$ is the set of all finite multisets (bags) over $S$.

> **Definition A.25 (Semantics of Type Expressions)**
> Let $\hat{T}$ be a set of types where the domain of each $t \in \hat{T}$ is $I(t)$. The semantics of type expressions $T_{Expr}(\hat{t})$ over $\hat{t}$ is defined for all $t \in \hat{t}$ as follows.
i. $I(t)$ is defined as given.
ii. $I(Set(t)) = F (I(t)) \cup \{ \bot \}$, 
$I(Bag(t)) = B (I(t)) \cup \{ \bot \}$.


#### A.2.5.3 Constructors

Operations for constructing collection values by enumerating their element values are called constructors. For types $t \in T_{Expr}(\hat{T}) $ constructors in $\Omega_{T_{Expr}(\hat{T})}$ are defined below. A parameter list $t \times \cdot \cdot \cdot \times t$ denotes $n (n \ge 0)$ parameters of the same type $t$. We define constructors $mkSet_t$ and $mkBag_t$ not only for any type $t$ but also for any finite number $n$ of parameters.
• $mkSet_t$ : $t \times \cdot \cdot \cdot \times t \rightarrow Set(t)$ 
• $mkBag_t$ : $t \times \cdot \cdot \cdot \times t \rightarrow Bag(t)$ 


The semantics of constructors is defined for values $v_1, \cdot \cdot \cdot , v_n \in I(t)$ by the following functions.
• $I(mkSet_t)(v_1, \cdot \cdot \cdot , v_n) = \{v_1, \cdot \cdot \cdot , v_n\}$
• $I(mkBag_t)(v_1, \cdot \cdot \cdot , v_n) = \{\{v_1, \cdot \cdot \cdot , v_n\}\}$


#### A.2.5.4 Collection Operations

The definition of operations of collection types comprises the set of all predefined collection operations. Operations common to the types $Set(t)$ and $Bag(t)$ are defined for the supertype $Collection(t)$. Table A.6 shows the operation schema for these operations. For all $t \in T_{Expr}( \hat{T})$, the signatures resulting from instantiating the schema are included in $\Omega_{T_{Expr}}( \hat{T})$ . The right column of the table illustrates the intended set-theoretic interpretation. For this purpose, $C$, $C_1$, $C_2$ are values of type $Collection(t)$, and $v$ is a value of type $t$.

Table A.6 - - Operations for type Collection(t)

|              | Signature                                                | Semantics                         |
| ------------ | -------------------------------------------------------- | --------------------------------- |
| size:        | $Collection(t) \rightarrow Integer$                      | $  \lvert C \rvert $              |
| count:       | $Collection(t) \times t \rightarrow Integer$             | $  \lvert C \cap \{ v \} \rvert $ |
| includes:    | $Collection(t) \times t \rightarrow Boolean$             | $ v \in C$                        |
| excludes:    | $Collection(t) \times t \rightarrow Boolean$             | $ v \notin C$                     |
| includesAll: | $Collection(t) \times Collection(t) \rightarrow Boolean$ | $ C_2 \subseteq C_1$              |
| excludesAll: | $Collection(t) \times Collection(t) \rightarrow Boolean$ | $ C_2 \cap C_1 = \emptyset$       |
| isEmpty:     | $Collection(t) \rightarrow Boolean$                      | $ C = \emptyset$                  |
| notEmpty:    | $Collection(t) \rightarrow Boolean$                      | $ C \ne \emptyset$                |
| sum:         | $Collection(t) \rightarrow t$                            | $ C \ne \emptyset$                |


The operation schema in Table A.6 can be applied to sets (bags) by substituting Set(t) (Bag(t)) for all occurrences of type Collection(t). A semantics for the operations in Table A.6 can be easily defined for each of the concrete collection types Set(t) and Bag(t). The semantics for the operations of Collection(t) can then be reduced to the concrete types because every collection type is either a set or a bag. Consider, for example, the operation count : $Set(t) \times t \rightarrow Integer$ that counts the number of occurrences of an element $v$ in a set $s$. The semantics of count is:
$$
I(count):(Set(t) \times t \rightarrow )(s,v) = 
\begin{cases}
1 \quad if \ v \in s, \\
0 \quad if \ v \notin s, \\
\bot \quad if s=\bot.
\end{cases}
$$

For bags , the meaning of count is

$$
I(count):(Bag(t) \times t \rightarrow )(\{\{ v_1, \cdot \cdot \cdot, v_n\}\},v) = 
\begin{cases}
0 \quad if \ n=0, \\
I(count)(\{\{ v_2, \cdot \cdot \cdot, v_n\}\},v) \quad if \ n>0 \ and \ v_1 \ne v, \\
I(count)(\{\{ v_2, \cdot \cdot \cdot, v_n\}\},v)+1 \quad if \ n>0 \ and \ v_1 = v.
\end{cases}
$$


As explained before, the semantics of count for values of type Collection(t) can now be defined in terms of the semantics of count for sets and bags.

$$
I(count) : (Collection(t) \times t \rightarrow Integer)(c,v) = 
\begin{cases}
I(count) : (Set(t) \times t \rightarrow Integer)(c,v) \quad if \ c \in I(Set(t)), \\
I(count) : (Bag(t) \times t \rightarrow Integer)(c,v) \quad if \ c \in I(Bag(t)).
\end{cases}
$$


#### A.2.5.5 Set Operations

Operations on sets include the operations listed in Table A.6. These are inherited from $Collection(t)$. Operations that are specific to sets are shown in Table A.7 where $S$, $S_1$, $S_2$ are values of type $Set(t)$, $B$ is a value of type $Bag(t)$ and $v$ is a value of type $t$.

Table A.7 - Operations for type $Set(t)$
|                      | Signature                                  | Semantics                       |
| -------------------- | ------------------------------------------ | ------------------------------- |
| union:               | $ Set(t) \times Set(t) \rightarrow Set(t)$ | $S_1 \cup S_2$                  |
| union:               | $ Set(t) \times Bag(t) \rightarrow Bag(t)$ | $S \cup B$                      |
| intersection:        | $ Set(t) \times Set(t) \rightarrow Set(t)$ | $S_1 \cap S_2$                  |
| intersection:        | $ Set(t) \times Bag(t) \rightarrow Set(t)$ | $S \cap B$                      |
| -:                   | $ Set(t) \times Set(t) \rightarrow Set(t)$ | $S_1 - S_2$                     |
| symmetricDifference: | $ Set(t) \times Set(t) \rightarrow Set(t)$ | $(S_1 \cup S_2)-(S_1 \cap S_2)$ |



#### A.2.5.6 Bag Operations

Operations for bags are shown in Table A.8, the operation asSequence is nondeterministic also for bags.

Table A.8 - Operations for type $Bag(t)$
|               | Signature                                  | Semantics      |
| ------------- | ------------------------------------------ | -------------- |
| union:        | $ Bag(t) \times Bag(t) \rightarrow Bag(t)$ | $B_1 \cup B_2$ |
| union:        | $ Bag(t) \times Set(t) \rightarrow Bag(t)$ | $B \cup S$     |
| intersection: | $ Bag(t) \times Bag(t) \rightarrow Bag(t)$ | $B_1 \cap B_2$ |
| intersection: | $ Bag(t) \times Set(t) \rightarrow Set(t)$ | $B \cap S$     |


### A.2.8 Data Signature

> **Definition A.28 (Data Signature)**
> Let $\hat{T}$ be the set of non-collection types: $\hat{T} = T_B \cup T_C \cup T_S$. The syntax of a data signature over an object model $M$ is a structure $\Sigma_M = (T_M, \Omega_M)$ where
i. $T_M = T_{Expr}(\hat{T})$
ii. $\Omega_M = \Omega_{T_{Expr}}(\hat{T}) \cup \Omega_B \cup \Omega_C \cup \Omega_S$.
The semantics of $\Sigma_M$ is a structure $I(\Sigma_M ) = (I(T_M), I( \Sigma_M ))$ where
i. $I(T_M)$ assigns each $t \in T_M$ an interpretation $I(t)$.
ii. $I(\Omega_M )$ assigns each operation $\omega : t_1 \times \cdot \cdot \cdot \times t_n \rightarrow t \in \Omega_M$ a total function $I(\omega) : I(t_1) \times \cdot\cdot\cdot \times I(t_n) \rightarrow I(t)$.



## A.3 OCL Expressions and Constraints

The core of OCL is given by an expression language. Expressions can be used in various contexts, for example, to define constraints such as class invariants and pre-/postconditions on operations. In this sub clause, we formally define the syntax and semantics of OCL expressions, and give precise meaning to notions like context, invariant, and pre-/ postconditions.

Sub clause A.3.1 defines the abstract syntax and semantics of OCL expressions and shows how other OCL constructs can be derived from this language core. The context of expressions and other important concepts such as invariants, queries, and shorthand notations are discussed.



### A.3.1 Expressions

we define the syntax and semantics of expressions. The definition of expressions is based upon the data signature we developed in the previous sub clause. A data signature $\Sigma_M = (T_M, \Omega_M)$ provides a set of types $T_M$ and a set of operations $\Omega_M$. The signature contains the initial set of syntactic elements upon which we build the expression syntax.


#### A.3.1.1 Syntax of Expressions
We define the syntax of expressions inductively so that more complex expressions are recursively built from simple structures. For each expression the set of free occurrences of variables is also defined. Also, each sub clause in the definition corresponds to a subclass of OCLExpression in the abstract syntax. The mapping is indicated.

> **Definition A.29 (Syntax of Expressions)**
> Let $\Sigma_M = (T_M, \Omega_M)$ be a data signature over an object model $M$. Let $Var = \{ Var_t \} \ t\in T_M$  be a family of variable sets where each variable set is indexed by a type t. The syntax of expressions over the signature $\Sigma_M$ is given by a set $Expr = {Expr_t}t \in T_M$ and a function $free : Expr \rightarrow F(Var)$ that are defined as follows.
> i. If $v \in Var_t$, then $v \in Expr_t$ and $free(v) := \{ v \}$.
> iii. (a) If $t \in T_M$ and $\omega: \rightarrow t \in \Omega_M$ then $\omega \in Expr_t$ and $undefined \in Expr_{OclVoid}$, and $free (\omega ) := \emptyset$ and $free(undefined) := \emptyset$.
>  $\quad$ (b) If $\omega: t_1 \times ... \times t_n \rightarrow t \in \Omega_M \ and \ e_i \in Expr_{t_i} \ for \ all i = 1, ... , n \ then \ \omega(e_1,..., e_n) \in Expr_t$ and $free(\omega (e_1,...,e_n)) := free
(e_1) \cup ... \cup free(e_n)$.
> vi. If $e_1 \in Expr_{Collection(t_1)}$, $v_1 \in Var_{t_1}$, $v_2 \in Var_{t_2}$, and $e_2, e_3 \in Expr_{t_2}$ then $e_1 \rightarrow iterate(v_1; v_2 = e_2 | e_3) \in Expr_{t_2}$ and $free(e_1 \rightarrow iterate(v_1; v_2 = e_2 | e_3)) := (free(e_1) \cup free(e_2) \cup free(e_3))-\{v1, v2 \}$.

A variable expression (i) refers to the value of a variable. Variables (including the special variable $self$) may be introduced by the context of an expression, as part of an iterate expression.

Constant expressions (iiia) refer to a value from the domain of a type. Operation expressions (iiib) apply an operation from $\Omega_M$ . The set of operations includes:
- predefined data operations: +, -, *, <, >, $size$, $max$
- attribute operations: $self.age$, $e.salary$
- navigation by role names: $self.employee$

As demonstrated by the examples, an operation expression may also be written in OCL path syntax as $e_1. \omega(e_2, ..., e_n)$. This notational style is common in many object-oriented languages. It emphasizes the role of the first argument as the
"receiver" of a "message". If $e_1$ denotes a collection value, an arrow symbol is used in OCL instead of the period: $e_1 \rightarrow \omega(e_2,..., e_n)$. Collections may be bags, sets.


An iterate expression (vi) is a general loop construct that evaluates an argument expression $e_3$ repeatedly for all elements of a collection that is given by a source expression $e_1$. Each element of the collection is bound in turn to the variable $v_1$
for each evaluation of the argument expression. The argument expression $e_3$ may contain the variable $v_1$ to refer to the current element of the collection. The result variable $v_2$ is initialized with the expression $e_2$ . After each evaluation of the argument expression $e_3$ , the result is bound to the variable $v_2$ . The final value of $v_2$ is the result of the whole iterate expression.

The iterate construct is probably the most important kind of expression in OCL. Many other OCL constructs (such as select, reject, collect, exists, forAll, and isUnique) can be equivalently defined in terms of an iterate expression (see sub clause A.3.1.3).

#### A.3.1.2 Semantics of Expressions


The semantics of expressions is made precise in the following definition. A context for evaluation is given by an environment $\pi = (\sigma, \beta)$ consisting of a system state $\sigma$ and a variable assignment $\beta : Var_t \rightarrow I(t)$. A system state $\sigma$ provides access to the set of currently existing objects, their attribute values, and association links between objects. A variable assignment $\beta$ maps variable names to values.



> **Definition A.30 (Semantics of Expressions)**
> Let Env be the set of environments $\pi = (\sigma, \beta)$. The semantics of an expression $e \in Expr_t$ is a function $I[[ e ]] : Env \rightarrow I(t)$ that is defined as follows.
> i. $I[[v]](r) = \beta(v)$.
> iii. $I[[undefined]] (r) = \bot$ and $I[[w]](r)=I(w)$.
> iv. $I[[w(e_1, ...,e_n)]](r) = I(w) (r) (I[[e_1]](r), ...,I[[e_n]](r))$.
> vii. $I[[ e_1 \rightarrow iterate(v_1;v_2 = e_2 | e_3)]] (r) = I[[e_1 \rightarrow iterate'(v_1 | e_3)]] (r')$ where $r' = (\sigma, \beta')$ and $r'' = (\sigma, \beta'')$ are environments with modified variable assignments $\beta' := \beta \{v_2 / I[[e_2]] (r) \}$ and $\beta'' := \beta' \{ v_2 / I[[e_3]] (\sigma, \beta' \{ v_1 / x_1 \} ) \}$, and $iterate'$ is defined as:
> (b) If $e_1 \in Expr_{Set(t1)}$ then
$$
I[[e_1 \rightarrow iterate'(v_1 | e_3)]] (r') = 
\begin{cases}
I[[v_2]] (r') \quad if \ I[[e_1]] (r') = \emptyset, \\
I[[mkSet_{t_1} (x_2,..., x_n) \rightarrow iterate'(v_1 | e_3)]] (r'') \quad if \ I[[e_1]] (r') = \{x_1,..., x_n \}.
\end{cases}
$$
> (c) If $e_1 \in Expr_{Bag(t1)}$ then
$$
I[[e_1 \rightarrow iterate'(v_1 | e_3)]] (r') = 
\begin{cases}
I[[v_2]] (r') \quad if \ I[[e_1]] (r') = \emptyset, \\
I[[mkBag_{t_1} (x_2,..., x_n) \rightarrow iterate'(v_1 | e_3)]] (r'') \quad if \ I[[e_1]] (r') = \{\{x_1,..., x_n \}\}.
\end{cases}
$$



The semantics of a variable expression (i) is the value assigned to the variable. An operation expression (iv) is interpreted by the function associated with the operation. Each argument expression is evaluated separately. The state $\sigma$ is passed to operations whose interpretation depends on the system state. These include, for example, attribute and navigation operations as defined in sub clause A.2.4.

An iterate expression (vii) loops over the elements of a collection and allows the application of a function to each collection element. The function results are successively combined into a value that serves as the result of the whole iterate expression. This kind of evaluation is also known in functional style programming languages as $fold$ operation.

In Definition A.30, the semantics of iterate expressions is given by a recursive evaluation scheme. Information is passed between different levels of recursion by modifying the variable assignment $\beta$ appropriately in each step. The interpretation of iterate starts with the initialization of the accumulator variable. The recursive evaluation following thereafter uses a simplified version of iterate, namely an expression iterate' where the initialization of the accumulator variable is left out, since this sub-expression needs to be evaluated only once. If the source collection is not empty, (1) an element from the collection is bound to the iteration variable, (2) the argument expression is evaluated, and (3) the result is bound to the accumulator variable. These steps are all part of the definition of the variable assignment $\beta''$. The recursion terminates when there are no more elements in the collection to iterate over. The constructor operations $mkBag_t$, and $mkSet_t$ are in $\Omega_M$ and provide the abstract syntax for collection literals like $Set {1,2}$ in concrete OCL syntax.

#### A.3.1.3 Derived Expressions Based on Iterate


A number of important OCL constructs such as $exists$, $forAll$, $select$, $reject$, $collect$, and $isUnique$ are defined in terms of iterate expressions. The following schema shows how these expressions can be translated to equivalent iterate expressions.

$$
\begin{aligned}
& I[[ e_1 \rightarrow exists(v_1 | e_3) ]](r) = I[[ e_1 \rightarrow iterate(v_1; v_2 = false | v_2 or e_3) ]](r)  \\
& I[[ e_1 \rightarrow forAll(v_1 | e_3) ]](r) = I[[ e_1 \rightarrow iterate(v_1; v_2 = true | v_2 and e_3) ]]( r)  \\
& I[[ e_1 \rightarrow select(v_1 | e_3) ]](r) = I[[ e_1 \rightarrow iterate(v_1; v_2 = e_1 | \ if \ e_3 \ then \ v_2 \ else \ v_2 \rightarrow excluding(v_1) \ endif) ]]( r)  \\
& I[[ e_1 \rightarrow reject(v_1 | e_3) ]](r) = I[[ e_1 \rightarrow iterate(v_1; v_2 = e_1 | \ if \ e_3 \ then \ v_2 \rightarrow excluding(v_1) \ else \ v_2 \ endif) ]]( r)  \\
& I[[ e_1 \rightarrow collect(v_1 | e_3) ]](r) = I[[ e_1 \rightarrow iterate(v_1; v_2 = mkBag _{type-of-e3} () | v_2 \rightarrow including(e_3) ) ]]( r)  \\
& I[[ e_1 \rightarrow isUnique(v_1 | e_3) ]](r) = I[[ e_1 \rightarrow iterate(v_1; v_2 = true | v_2 \ and \ e_1 \rightarrow count(v_1)=1 ) ]]( r) 
\end{aligned}
$$


#### A.3.1.4 Expression Context

An OCL expression is always written in some syntactical context. Since the primary purpose of OCL is the specification of constraints on a UML model, it is obvious that the model itself provides the most general kind of context. In our approach, the signature $\Sigma_M$ contains types (e.g., object types) and operations (e.g., attribute operations) that are "imported" from a model, thus providing a context for building expressions that depend on the elements of a specific model.

On a much smaller scale, there is also a notion of context in OCL that simply introduces variable declarations. This notion is closely related to the syntax for constraints written in OCL. A context clause declares variables in invariants.

A $context$ of an invariant is a declaration of variables. The variable declaration may be implicit or explicit. In the implicit form, the context is written as

$$context \ C \ inv: <expression>$$

In this case, the $<expression>$ may use the variable $self$ of type $C$ as a free variable. In the explicit form, the $context$ is written as

$$ context \ v_1 : C_1, ... , v_n : C_n \ inv:
<expression> $$

The $<expression>$ may use the variables $v_1, ... , v_n$ of types $C_1,..., C_n$ as free variables.


#### A.3.1.5 Invariants
An invariant is an expression with Boolean result type and a set of (explicitly or implicitly declared) free variables $v_1 : C_1,..., v_n : C_n$ where $C_1,..., C_n$ are classifier types. An invariant

$$ context \ v_1 : C_1, ... , v_n : C_n \ inv:
<expression> $$


is equivalent to the following expression without free variables that must be valid in all system states.

$$
\begin{aligned}
& C_1.allInstances \rightarrow forAll(v_1 : C_1 | \\
& \quad ... \\
& \quad C_n.allInstances \rightarrow forAll(v_n:C_n ) |\\
& \quad \quad <expression>\\
& \quad )\\
& \quad ...\\
& )\\
\end{aligned}
$$

A system state is called valid with respect to an invariant if the invariant evaluates to true. Invariants with null or invalid result invalidate a system state.
