/*
  ===============================================
  DCC831 Formal Methods
  2023.2

  Mini Project 2 - Part B

  Your name(s): Guilherme de Oliveira Silva
  ===============================================
*/

class Buffer<T(0)>
{
  //------------------------------------------
  // Abstract state
  //------------------------------------------
  // the sequence of elements in the buffer,
  // from oldest to newest
  ghost var Contents: seq<T>
  // the capacity of the buffer
  ghost var Capacity: nat

  //------------------------------------------
  // Concrete state
  //------------------------------------------
  // the elements in the buffer are stored in a
  var a: array<T>
  // position of the oldest element in the buffer
  var front: nat
  // the current number of elements in the buffer
  var size: nat

  // class invariant
  ghost predicate Valid()
    reads this
  {
    // concrete state invariants (to be provided)
    0 <= this.front <= this.size < this.a.Length &&

    // connection between abstract and concrete state
    Capacity == a.Length &&
    size == |Contents| &&
    Contents == if front + size < Capacity then a[front .. front+size]
                else a[front ..] + a[0 .. (front + size - Capacity)]
  }

  constructor init(n: int)
    requires n > 0
    ensures Contents == []
    ensures Capacity == n
    ensures Valid()
  {
    Contents := [];
    Capacity := n;
    this.a := new T[n];
    this.size := 0;
    this.front := 0;
  }

  function isEmpty() : bool
    reads this
    requires Valid()
    ensures isEmpty() <==> Contents == []
  {
    this.size == 0
  }

  function isFull() : bool
    reads this
    requires Valid()
    ensures isFull() <==> |Contents| == Capacity
  {
    this.size == a.Length
  }

  method get() returns (d: T)
    modifies a
    requires Valid()
    requires !isEmpty()
    ensures Valid()
    ensures old(Contents) == [d] + Contents
    ensures Capacity == old(Capacity)
  {
    var newArray := new T[a.Length];
    var i : int := 0;
    d := a[front];
  }

  method put(d: T)
    requires Valid()
    requires !isFull()
    ensures Valid()
    ensures Contents == old(Contents) + [d]
    ensures Capacity == old(Capacity)
  {

  }
}
