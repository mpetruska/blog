---
title: Conjunctive pattern matching in Scala
tags: Scala pattern-matching
excerpt_separator: "{% comment %} end excerpt {% endcomment %}"
layout: post
---

Combining Scala extractor objects with `&`.

{% comment %} end excerpt {% endcomment %}

[tl;dr](#solution)

In business applications sometimes developers end up with types
that contain plenty of fields. Let's create an example type with
a few fields:

{% highlight Scala %}

case class User(username: String, emailAddress: String, ...)

{% endhighlight %}

Since the "record" is growing/changing as development of the
application proceeds, it quickly becomes impractical to use
standard pattern matching against the generated extractor
method (`User.unapply`).

{% highlight Scala %}

user match {
  case User(name, _, _, _, ...) =>
}

{% endhighlight %}
{% comment %} ,_ {% endcomment %}

Every change to the `User` type that re-orders, adds or removes
fields will make it necessary to also change the pattern matches...
all of them.
The solution to this problem is to create custom extractor objects
that can also evaluate elaborate logic to control the flow of the
application. Some examples:

{% highlight Scala %}

object HasUsername {
  def unapply(x: User): Option[String] = Some(x.username)
}

object HasConfirmedEmailAddress {
  def unapply(x: User): Boolean = ...
}

{% endhighlight %}

With these, the above pattern matching construct becomes much more
readable and maintainable:

{% highlight Scala %}

user match {
  case HasUsername(name) =>
}

{% endhighlight %}

The downside is that combining the two matches seems more complicated
now. The basic idea is to create a new extractor that is parametrized
by two others, and combines them with the logical `and`
operation; hence the name `&` seems appropriate. Let's create
the extractor on top of functions, for simplicity's sake.

{% highlight Scala %}

case class &[X, A, B](e1: X => Option[A], e2: X => Option[B]) {
  def unapply(x: X): Option[(A, B)] = for {
    v1 <- e1(x)
    v2 <- e2(x)
  } yield v1 -> v2
}

{% endhighlight %}

Now we can call it like this:

{% highlight Scala %}

val myExtractor = &(HasUsername.unapply, HasUsername.unapply)

user match {
  case myExtractor(a, b) =>
}

{% endhighlight %}

The problems with this syntax are quite apparent. First of all, the
combined extractor has to be created upfront and cannot be built
ad-hoc, as needed. Second, the `&` constructor only accepts "extractors"
(functions that return `Option[_]`) and no predicates. So, if we want
to create a combinator to address these issues, it needs to be an `object`
that does not accept parameters. Additionally it needs to be unaware
of the types of the extractors combined.

If we pattern-matched on a tuple (or collection) with identical
elements instead of a single value, we would only need to de-structure the
tuple in addition to calling the extractors:

{% highlight Scala %}

(user, user) match {
  case (HasUsername(name), HasConfirmedEmailAddress()) =>
}

{% endhighlight %}

Unfortunately, duplicating the values in the head of the match
is really unwieldy; but duplicating the values to be matched can
easily be done with an extractor (similar to the `&` above):

<a name="solution"></a>

{% highlight Scala %}

object & {
  def unapply[X](x: X): Option[(X, X)] = Some((x, x))
}

{% endhighlight %}

This version is very simple, and actually solves our initial
problem:

{% highlight Scala %}

user match {
  case HasUsername(name) & HasConfirmedEmailAddress() =>
}

{% endhighlight %}

Note that instead of the prefix syntax `&(_, _)` scala allows
the use of the infix syntax `_ & _` automatically for functions,
case classes and objects with symbolic names.

### Mathematical proof

... for those interested.

Let's walk through the above structure in a mathematical formalism,
to develop some confidence. I'll be using the [Coq theorem prover][Coq]
to aid me in stating and proving some properties of the combinator.

[Coq]: https://en.wikipedia.org/wiki/Coq

The mathematical proof of the pattern matching construct above
is uninteresting, but the way we can state properties of the code
formally is useful.

Since we do not have the formal language specification of Scala in
Coq available, we will implement the Scala pattern matching constructs
and its the semantics based on intuition. (Also note that this means
that the proofs we're doing are not full specifications by themselves,
they rely on some implicit axioms.)

To model a general Scala match, we first need to describe the `case` part,
which models the condition and the parameters that are bound.
We could just use a function `A -> B` for this, but
Scala allows two types of conditionals; hence we need to create an inductive type
with two cases. This type should be indexed over the type of the matched value
and the type of the bound parameters.

{% highlight Coq %}

Inductive scala_case_condition : Set -> Set -> Type :=
  | case_pred    : forall A : Set,   (A -> bool)     -> scala_case_condition A A
  | case_extract : forall A B : Set, (A -> option B) -> scala_case_condition A (A * B).
  
{% endhighlight %}

The first (non-type) parameter for each constructor is the function that
matches (and in the extract case also binds) against the "incoming" value.
I chose to also include the original value in the bound parameters list.

A full `case` specification consists of the matcher/binder and the body of the case.
We will represent the body with a function; putting these parts together:

{% highlight Coq %}

Inductive scala_case : Set -> Set -> Type :=
  | case : forall A B C : Set, scala_case_condition A B -> (B -> C) -> scala_case A C.

{% endhighlight %}

The last piece of the puzzle is the whole `match` construct, which models
the whole expression. Here I chose not to include the matched value in the
construct, it will be provided to the evaluation function as a parameter.
So instead of `x match {}`, we model `_ match {}`. This does not effect
the formalism much, it's purpose is to make it clear that a match is a function.

{% highlight Coq %}

Inductive scala_match (A B : Set) : Type :=
  | match_constr : list (scala_case A B) -> scala_match A B.

{% endhighlight %}

Since we will want to prove some properties of the (not yet constructed)
match "combinator", we will need to implement the semantics for the models.

Let us start with evaluating a condition. Since the constructors of
`scala_case_condition` have dependent types, it will be easier to implement
`eval_case_condition` with the help of [tactics][coqtactics].

{% highlight Coq %}

Definition eval_case_condition : forall (A B : Set), A -> scala_case_condition A B -> option B.
  intros A B a cond;
  inversion cond as [ A0 p | A0 C e ].
  - subst A0 B; exact (if p a then Some a else None).
  - subst A0;   exact (option_map (fun c => (a, c)) (e a)).
Defined.

{% endhighlight %}

The curious reader can issue a `Print eval_case_condition.` command to see
why I recommended the implementation via tactics route.

Implementing `eval_case` should also be done with tactics:

{% highlight Coq %}

Definition eval_case : forall (A B : Set), A -> scala_case A B -> option B.
  intros A B a case.
  inversion case as [ A0 C B0 cond f ]. subst A0 B0.
  exact (option_map f (eval_case_condition a cond)).
Defined.

{% endhighlight %}

... but the implementation of `eval_match` can be done relatively
easily in [Gallina][coqgallina]:

{% highlight Coq %}

Definition eval_match (A B : Set) (a : A) (m : scala_match A B) : option B :=
  match m with
  | match_constr cases =>
      (fix loop cs :=
          match cs with
          | nil      => None
          | cons h t =>
              match eval_case a h with
              | Some b => Some b
              | None   => loop t
              end
          end) cases
  end.

{% endhighlight %}

We can take this model to a test ride to see if it really
looks like a Scala match:

{% highlight Coq %}

Record user : Set := mkUser {
    username     : string;
    emailAddress : string
  }.

Definition username_extractor (u : user) : option string := Some (username u).
Definition tru (u : user) : bool := true.
Definition fls (u : user) : bool := false.

Open Scope string_scope.

Eval compute in (
  eval_match (mkUser "username" "")
    (match_constr  (
      case (case_pred fls) (fun _ => "fls") ::
      case (case_extract username_extractor) snd ::
      case (case_pred tru) (fun _ => "tru") ::
      nil)
    )
).

(*  = Some "username"
     : option string  *)

{% endhighlight %}
{% comment %} (* {% endcomment %}

Now we can try and "emulate" the `&` matching construct.

{% highlight Coq %}

Definition and_match : forall A B X Y : Set,
    scala_case_condition A X -> scala_case_condition A Y -> (X -> Y -> B) -> scala_case A B.

{% endhighlight %}

Basically this operation follows the structure of the Scala version:
It accepts two conditions which match on the same value (typed `A`), and the
case body can use both variables (typed `X` and `Y`) that are bound by the
case conditions; hence the type of the body will be `X -> Y -> B`.
The implementation of the `and` construct is also done via tactics, which I won't
unfold here. It is however available in the full proof script (see link below).

Now after all this prelude we can state (and prove) the main theorems about
the `&` construct:

{% highlight Coq %}

Theorem and_match_both_match : forall (A B X Y : Set) (a : A) (f : X -> Y -> B)
    (c1 : scala_case_condition A X) (c2 : scala_case_condition A Y),
    case_matches a (and_match c1 c2 f) <-> cond_matches a c1 /\ cond_matches a c2.

{% endhighlight %}

After the first two lines (which essentially just introduce the variables),
the theorem proves the main property, namely that `&` matches if and only if
both the cases match.

The proof of the theorem is highly involved; I advise every interested reader
to step through the script in `coqtop`, `CoqIde`, `Proof General` or `JsCoq`.
Also note that the script is deliberately chatty to ease reading and exploring.

The full interactive script (with proofs) is available at
[CollaCoq][fullinteractive] (please load the package `color` from
the bottom right list).

The non-interactive version is available on the
[github source of the blog][githubcoqsource].

Thanks for your time and have fun,  
Mark

[coqtactics]:      https://coq.inria.fr/doc/tactics.html
[coqgallina]:      https://coq.inria.fr/refman/gallina.html
[fullinteractive]: https://x80.org/collacoq/votuwuwife.coq
[githubcoqsource]: https://github.com/mpetruska/blog/blob/master/sources/2018-01-26-scala-pattern-matching-and.v

