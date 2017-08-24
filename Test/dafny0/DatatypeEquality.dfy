// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype State = State(m:map<int, bool>)

lemma Test(s:State)
requires 42 in s.m
ensures s.(m := s.m[42 := s.m[42]]) == s
{
var s' := s.(m := s.m[42 := s.m[42]]);
// assert s'.m == s.m;
}


datatype D<A,B> = D1(a: A) | D2(b: B)

lemma DTest<A, B>(x: D<A,B>, y: D<A, B>) 
    requires x.D1? ==> y.D1? && x.a == y.a
    requires x.D2? ==> y.D2? && x.b == y.b
{
}

datatype Option<A> = None | Some(x: A)

datatype L<A> = L(x: Option<(A, L<A>)>)

function concat<A>(xs: L<A>, ys: L<A>): L<A>
{
    match xs.x
        case None => L(None)
        case Some(p) => L(Some((p.0, concat(p.1, ys))))
}

function reverse<A>(xs: L<A>): L<A>
{
    match xs.x
        case None => L(None)
        case Some(p) => concat(reverse(p.1), L(Some((p.0, L(None)))))
}

lemma concat_assoc<A>(xs: L<A>, ys: L<A>, zs: L<A>)
    ensures concat(concat(xs, ys), zs) == concat(xs, concat(ys, zs))
{
    match xs.x
        case None =>
        case Some(p) =>
}
