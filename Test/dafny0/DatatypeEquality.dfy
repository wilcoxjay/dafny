// RUN: /nologo /print:tmp.bpl /compile:0

datatype State = State(m:map<int, bool>)

lemma Test(s:State)
requires 42 in s.m
ensures s.(m := s.m[42 := s.m[42]]) == s
{
var s' := s.(m := s.m[42 := s.m[42]]);
// assert s'.m == s.m;
}
