/-!
# 目录

- IndutiveTypes: 主要介绍 `inductive` 关键词，如何自己定义类型，也就是数学对象。
- PatternMatching: 主要介绍如何使用 `match` 来操作在上一节中定义的类型。
- Recursion：主要介绍如何使用Lean实现递归函数。
- Induction：主要介绍如何使用数学归纳法进行证明。
- Structure：主要介绍 `structure` 关键词。

-/

section InductiveTypes
/-!
# 归纳类型

我们已经知道Lean中的基本类型与宇宙层级，如 `Prop`、`Type`、`Type 1`等类型，以及使用 `→` 构造的函数类型，
一个自然而然的问题就是，如 `Nat`、`Bool` 这类基础类型是如何构造的。
它们属于**归纳类型**这一大分支，本节我们将展示如何自行定义一个归纳类型，并在定理证明中使用它。

首先我们明确一点：**定义一个类型即定义这个类型的值的构造方式**。
不同的构造方式即对应着不同的值，值之间的区别就是构造方式之间的区别。

我们首先来看一个相对简单的例子，即只有有限个值的类型，典型例子如 `Bool`，只有两个可能的值，即 `true` 与 `false`。
在其他编程语言中，这种类型也被称为枚举类型，一般用 `enum` 关键词声明，但在Lean中它们也是归纳类型，
用 `inductive` 关键词声明。
-/

-- 声明 `Color` 类型，仅有红黄蓝三种值
inductive Color where
 | Red    : Color
 | Yellow : Color
 | Blue   : Color

-- 列举多种其他的语法

#print Color
/-!
目前我们知道如何定义一个能够依靠枚举列出所有可能的值的类型，但这显然远远无法满足我们的需求。
下一步，我们要从有限向无限迈进，如何做到这一点？我们需要从constructor入手。
-/

/-
inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : Nat
Nat.succ : Nat → Nat
-/
#print Nat

#check Nat.zero
#check Nat.succ

/-
现在我们有了无限，但若对无限做进一步拆解，我们的无限的基数也仅是阿列夫零。
在仅涉及其本身的语境中进行无穷递归得到的无限，终究只是个小小的闭包，离视域之外不可数的精彩世界还差一步。
让我们在一个类型的constructor中加入其他类型。
-/

-- 声明 `NatList` 类，为元素类型为 `Nat` 的列表
inductive NatList where
  | nil  : NatList
  | cons : Nat → NatList → NatList

-- 声明 `Student` 类，包含该学生的姓名、年龄、成绩
inductive Student where
  | mk : String → Nat → Nat → Student

structure Student' where
  name  : String
  age   : Nat
  grade : Nat

#check Student.mk
#check Student'.mk
#check Student'.name
#check Student'.age
#check Student'.grade


-- 依赖归纳类型
inductive List' (α : Type) where
  | nil  : List' α
  | cons : α → List' α → List' α

inductive MyOr (a b : Prop) : Prop where
  | inl : a → MyOr a b
  | inr : b → MyOr a b

inductive Option' (α : Type) where
  | none : Option' α
  | some : α → Option' α

end InductiveTypes

section PatternMatching
/-!
# 模式匹配

现在，我们讨论如何在实际编程或证明中使用归纳类型。
这涉及到在函数式语言中常见的**模式匹配**机制，即 `match` 关键词。
我们将对上一节中的每个例子分别使用 `match` 实现一些函数。
-/

-- 将 `Color` 类型的值转换为数值
-- 使用 if ... then ... else
def color2num (c : Color) : Nat := sorry

-- 使用 `match`
def color2num' (c : Color) : Nat := sorry

-- 省略 `match`
def color2num'' : Color → Nat := sorry

-- 使用 `_` 作为占位符表示其它情况
-- 判断两个 `Color` 是否依次为 `Red` 和 `Blue`
def isRedAndBlue : Color → Color → Bool := sorry

-- 定义自然数的前驱
def pred : Nat → Nat := sorry

-- 实现 `Student`类几个属性的取用
def Student.name : Student → String := sorry
def Student.age : Student → Nat := sorry
def Student.grade : Student → Nat := sorry

-- 拿到 `List'` 的最后一个值
def List'.end {α : Type} : List' α → Option' α := sorry

-- 构造 `MyOr`
def MyOr.intro_left {a : Prop} (b : Prop) (h : a) : MyOr a b := sorry
def MyOr.intro_right {b : Prop} (a : Prop) (h : b) : MyOr a b := sorry

-- `MyOr` 的 `resolve`
def MyOr.resolve_left {a b : Prop} (h : MyOr a b) (ha : ¬a) : b := sorry
def MyOr.resolve_right {a b : Prop} (h : MyOr a b) (hb : ¬b) : a := sorry

end PatternMatching

section Recursion

/-!
# 递归函数

我们会在本节中介绍自然数相关的一些递归函数的定义，以及函数式编程中经典的 `map`、`filter`、`fold` 函数，
希望能让读者对函数式编程有一些基本的感觉。

首先我们要清楚函数式编程与命令式编程的区别。虽然**函数**这个词在数学与计算机中都有着各自的定义，
但不严格地说，许多人对函数的印象就是输入一些东西，输出另一些东西，这么看来数学上的函数和计算机中的函数似乎没有区别。
然而，往细节看，两者完全不是一个东西。在数学上，如果 $f$ 是一个函数，那么 $f(x)$ 被视为输入 $x$ 后得到的一个值。
而在计算机中，如果 `f` 是一个函数，那么 `f(x)` 被视为 `f` 接收 `x` 作为参数后执行的函数调用，
类似一个**动作**，而非一个**值**。而动作会产生副作用，具体而言就是对计算机内存中维护的程序状态进行一定的修改。

在函数式编程中，两种函数的区别被无限缩小了。一个Lean中的函数可以被视为一个数学上的函数，因为它的作用就是计算得值，
并且没有副作用，我们不用像命令式编程中一样考虑函数定义中每个语句可能会造成什么影响，
事实上Lean中的函数定义就像数学中一样，是在描述一个计算过程。
-/

-- 阶乘
def fac : Nat → Nat := sorry

-- 组合数
def choose : Nat → Nat → Nat := sorry

-- Fibonacci数列 (留做练习)
def fib : Nat → Nat := sorry

-- 最大公因式
def gcd (m n : Nat) : Nat := sorry

example : gcd 3 6 = 3 := sorry

-- 对列表中每个元素加一
def addOne : List Nat → List Nat := sorry

-- map
def map {α β : Type} (l : List α) (f : α → β) : List β := sorry

-- filter
def filter {α : Type} (l : List α) (f : α → Bool) : List α := sorry

-- foldr
-- def foldr {α β : Type} (f : α → β → β) (l : List α) (init : β) : β := sorry

-- foldl
-- def foldl {α β : Type} (f : α → β → α) (init : α) (l : List β)  : α := sorry


section Exercise
variable {α : Type}
-- 思考题
/- 写一个类型为 `(α → Bool) → List α → Bool` 的名为 `exist` 的函数，
用于判断一个列表中是否存在满足条件的元素，并通过以下测试：-/

def exist : (α → Bool) → List α → Bool := sorry

-- #eval exist (fun x => x > 4) [1,2,3]           -- false
-- #eval exist (fun x => x.length < 10) ["10000"] -- true

/-任选一种排序算法实现自然数列表的升序排序，函数名为 `sort`，类型为 `List α → List α`，并通过以下测试：-/

def sort : List α → List α := sorry
-- #eval sort [3, 2, 1, 4, 2, 1] -- [1, 1, 2, 2, 3, 4]

end Exercise
end Recursion

section Induction

/-！
# 数学归纳法

Lean中的定理实际上就是返回值为命题证明的函数，使用数学归纳法证明定理，实际上就是在函数定义中进行递归调用并
能证明该函数是停机的。因此，我们完全可以使用 `match` 关键词来进行数学归纳法证明。
-/

-- 证明阶乘是正的
theorem fac_pos (n : Nat) : fac n > 0 := sorry

-- 另一种写法
theorem fac_pos' : ∀ n : Nat, fac n > 0 := sorry

-- 使用 `induction`
theorem fac_pos'' (n : Nat) : fac n > 0 := sorry

end Induction

section Example

inductive Nat' where
  | zero : Nat'
  | succ : Nat' → Nat'

def Nat'.add : Nat' → Nat' → Nat'
  | .zero, n   => n
  | .succ k, n => .succ (k.add n)

def Nat'.mul : Nat' → Nat' → Nat'
  | .zero, _   => .zero
  | .succ k, n => n.add (k.mul n)

theorem Nat'.add_zero : ∀ n : Nat', n.add .zero = n
  | .zero   => rfl
  | .succ k => by rw [Nat'.add, Nat'.add_zero]

theorem Nat'.add_succ : ∀ m n : Nat', m.add n.succ = (m.add n).succ
  | .zero, _   => by rw [Nat'.add, Nat'.add]
  | .succ k, _ => by rw [Nat'.add, Nat'.add, Nat'.add_succ]

theorem Nat'.add_comm : ∀ m n : Nat', m.add n = n.add m := sorry

theorem Nat'.add_assoc : ∀ a b c : Nat', (a.add b).add c = a.add (b.add c) := sorry

-- 以下留做练习
theorem Nat'.mul_zero : ∀ n : Nat', n.mul .zero = .zero
  | .zero   => by rw [Nat'.mul]
  | .succ k => by rw [Nat'.mul, Nat'.add, Nat'.mul_zero]

theorem Nat'.mul_succ : ∀ m n : Nat', m.mul n.succ = m.add (m.mul n)
  | .zero, _   => by rw [Nat'.mul, Nat'.add, Nat'.mul]
  | .succ k, _ => by
    rw [Nat'.mul, Nat'.mul, Nat'.add, Nat'.add, Nat'.mul_succ]
    rw [← Nat'.add_assoc, Nat'.add_comm _ k, Nat'.add_assoc]

theorem Nat'.add_mul : ∀ a b c : Nat', (a.add b).mul c = (a.mul c).add (b.mul c) := sorry

theorem Nat'.mul_comm : ∀ m n : Nat', m.mul n = n.mul m := sorry

theorem Nat'.mul_assoc : ∀ a b c : Nat', (a.mul b).mul c = a.mul (b.mul c) := sorry


end Example

section Structure

/-!
# 结构体的创建

在本节中，我们将更详细地介绍 `structure` 关键词。相比先前所讲的用 `inductive` 实现的近似，在实际情况中我们
更常使用 `structure`，因为Lean提供了许多额外的便利功能，我们将用例子进行详细介绍。

首先我们从一个简单的情境出发，假设我们正在为学校的数据库确定学生数据模型，在最开始，我们只关心学生的名字与学号，
也就是说，我们在Lean中定义的 `Student` 类型只需有两个属性：`name` 与 `id`。
-/

structure Student'' where
  name : String
  id   : Nat
deriving Repr

#check Student''.mk
#check Student''.name
#check Student''.id

#eval Student''.mk "Bob" 20242024
#eval (⟨"Bob", 20242024⟩ : Student'')
#eval ({name := "Bob", id := 20242024} : Student'')

def Bob : Student'' := ⟨"Bob", 20242024⟩
def Bob' : Student'' := {
  name := "Bob"
  id   := 20242024
}
def Bob'' : Student'' := Student''.mk "Bob" 20242024

example : Bob = Bob' := rfl
example : Bob = Bob'' := rfl

-- 我们要求该结构自带一个性质：学生学号必为8位数字，任何一个合法的term都应当满足这一性质。
-- 我们通过 `extends` 关键词来创建一个面向对象意义下的子类，即拥有 `Student''` 的所有字段，并有着新的性质的类型。

structure ValidStudent extends Student'' where
  -- 此处 `:=` 后为该字段默认值，对于命题字段使用 `by` 表示尝试使用tactic进行证明，如果无法证明则抛出错误要求手动提供。
  isValid : (Nat.toDigits 10 id).length = 8 := by decide
deriving Repr

#check ValidStudent.mk
#check ValidStudent.toStudent''
#check ValidStudent.isValid

#eval ValidStudent.mk Bob
#eval ValidStudent.mk ⟨"Bob", 20242024⟩
#eval ({toStudent'' := Bob} : ValidStudent)

/-
考虑到有时类型的继承中会出现如下的情形：
    A
  /   \
B       C
  \   /
    D
如若我们不使用 `extends`，而是手动在结构定义中使用 `toB` 和 `toC`，构造时分别提供 `B` 和 `C` 的具体对象，
那么就存在这两个同样继承于 `A` 的对象的 `A` 的字段数据不同的问题。
-/

structure A where
  x : Nat

structure B where
  toA : A
  y   : Nat

structure C where
  toA : A
  z   : Nat

structure D where
  toB : B
  toC : C

#check D.mk

def b : B := ⟨⟨1⟩, 2⟩
def c : C := ⟨⟨2⟩, 3⟩
def d : D := ⟨b, c⟩

#eval d.toB.toA
#eval d.toC.toA

-- `extends` 用一些魔法帮助我们避免了这一问题。

structure B' extends A where
  y : Nat

structure C' extends A where
  z : Nat

structure D' extends B, C

example : ∀ d : D', d.toA = d.toC.toA := by
  intro d
  rfl

structure Point (α : Type) where
  x : α
  y : α

-- `.mk` 用于创建term，依赖类型自动变为隐式参数
#check Point.mk

/-
值得一提的是，Lean中的 `Subtype` 就是用 `structure` 定义的，以下是定义源码：

structure Subtype {α : Sort u} (p : α → Prop) where
  /-- If `s : {x // p x}` then `s.val : α` is the underlying element in the base
  type. You can also write this as `s.1`, or simply as `s` when the type is
  known from context. -/
  val : α
  /-- If `s : {x // p x}` then `s.2` or `s.property` is the assertion that
  `p s.1`, that is, that `s` is in fact an element for which `p` holds. -/
  property : p val

注意，`Subtype p` 是一个依赖类型，跟我们先前的 `Student` 是一个层级的，类型为 `Subtype p` 的term与先前
的 `Bob` 是同一层级的。使用不同的 `p` 可以派生出无穷多的 `Subtype`。
-/

#check Subtype
#check Subtype fun x => x < 1
#check Subtype.mk
#check (⟨1, by decide⟩ : Subtype (fun x => x > 0))
#check (⟨Bob, by decide⟩ : Subtype (fun s => s.name = "Bob"))
#check (⟨(⟨"Bob", 20242024⟩ : Student''), by decide⟩ : Subtype (fun s => s.name = "Bob"))

end Structure
