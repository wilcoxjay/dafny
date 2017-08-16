// RUN: %dafny /compile:3 /spillTargetCode:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype Byte = x | 0 <= x < 256
predicate method GoodByte(b: Byte) {
  b % 3 == 2
}
predicate method GoodInteger(i: int) {
  i % 5 == 4
}

predicate method GoodChar(c: char) {
  'a' <= c <= 'z'
}

predicate method GoodString(s: string) {
    |s| > 0 && s[0] == 'x'
}

predicate t(x: int) {
    true
}
lemma PairExists()
    ensures exists p: (int, int) :: 0 <= p.0 <= 10 && 0 <= p.1 <= 10
{
    var _ := (1, 1);
}

lemma SingletonExists()
    ensures exists l: seq<int> :: |l| > 0 && 0 <= l[0] <= 10
{
    var _ := |[1]|;
}

method Main() {
  assert GoodByte(11) && GoodInteger(24);
  var b: Byte :| GoodByte(b);
  var i: int :| 0 <= i < 256 && GoodInteger(i);
  print "b=", b, "  i=", i, "\n";
  var m0 := new MyClass;
  var m17 := new M17.AnotherClass;

  var b2: bool :| b2;
  assert GoodChar('q');
  var c: char :| GoodChar(c);
  var z: int :| z > 100;
  assert GoodString("xylophone");
  var my_strings: seq<string> := ["hello", "xylophone", "abc"];
  var s: string :| s in my_strings && GoodString(s);

  PairExists();
  var p: (int, int) :| 0 <= p.0 <= 10 && 0 <= p.1 <= 10;

  SingletonExists();
  var l: seq<int> :| |l| > 0 && 0 <= l[0] <= 10;
}

class MyClass { }

module M17 {
  class AnotherClass { }
}
