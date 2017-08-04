// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<T> = Nil | Cons(head: T, tail: List)

predicate method sorted(l: List<int>)
{
  match l
  case Nil => true
  case Cons(x, rest) =>
    match rest
    case Nil => true
    case Cons(y, _) => x <= y && sorted(rest)
}

// Number of occurrences of z in l
function method nb_occ(z: int, l: List<int>): nat
{
  match l
  case Nil => 0
  case Cons(z', l') =>
    (if z == z' then 1 else 0) + nb_occ(z, l')
}

function method contents(l: List<int>): seq<int>
{
  match l
  case Nil => []
  case Cons(z, l') => [z] + contents(l')
}

// list l' is a permutation of list l
predicate method equiv(l: List<int>, l': List<int>)
{
  forall z: int | z in contents(l) :: nb_occ(z, l) == nb_occ(z, l')
}

// equiv is an equivalence
lemma equiv_refl(l: List<int>)
  ensures equiv(l, l);
{
}

lemma equiv_sym(l: List<int>, l': List<int>)
  requires equiv(l, l');
  ensures equiv(l', l);
{
}

lemma equiv_trans(l: List<int>, l': List<int>, l'': List<int>)
  requires equiv(l, l') && equiv(l', l'');
  ensures equiv(l, l'');
{
}

lemma equiv_cons(z: int, l: List<int>, l': List<int>)
  requires equiv(l, l');
  ensures equiv(Cons(z, l), Cons(z, l'));
{
}

lemma equiv_perm(a: int, b: int, l: List<int>, l': List<int>)
  requires equiv(l, l');
  ensures equiv(Cons(a, Cons(b, l)), Cons(b, Cons(a, l')));
{
  var L, L' := Cons(a, Cons(b, l)), Cons(b, Cons(a, l'));
  forall z {
    calc {
      nb_occ(z, L);
      (if z == a && z == b then 2 else if z == a || z == b then 1 else 0) + nb_occ(z, l);
      (if z == a && z == b then 2 else if z == a || z == b then 1 else 0) + nb_occ(z, l');
      nb_occ(z, L');
    }
  }
}

// insertion of z into l at the right place (assuming l is sorted)
function method aux(z: int, l: List<int>): List<int>
{
  match l
  case Nil => Cons(z, Nil)
  case Cons(a, l') =>
    if z <= a then Cons(z, l) else Cons(a, aux(z, l'))
}

// the aux function seems to be a good tool for sorting...

lemma aux_equiv(l: List<int>, x: int)
  ensures equiv(Cons(x, l), aux(x, l));
{
  match l {
    case Nil =>
    case Cons(_, _) =>
  }
}

lemma aux_sorted(l: List<int>, x: int)
  requires sorted(l);
  ensures sorted(aux(x, l));
{
  match l {
    case Nil =>
    case Cons(_, l') =>
      match l' {
        case Nil =>
        case Cons(_, _) =>
      }
  }
}

// the sorting function
function method sort(l: List<int>): List<int>
  ensures var l' := sort(l); equiv(l, l') && sorted(l');
{
  existence_proof(l);
  var l' :| equiv(l, l') && sorted(l'); l'
}

lemma existence_proof(l: List<int>)
  ensures exists l' :: equiv(l, l') && sorted(l');
{
  match l {
    case Nil =>
      assert sorted(Nil);
    case Cons(x, m) =>
      existence_proof(m);
      var m' :| equiv(m, m') && sorted(m');
      calc ==> {
        equiv(m, m') && sorted(m');
        equiv(l, Cons(x, m')) && sorted(m');
        { aux_equiv(m', x); }
        equiv(l, aux(x, m')) && sorted(m');
        { aux_sorted(m', x); }
        equiv(l, aux(x, m')) && sorted(aux(x, m'));
      }
  }
}
