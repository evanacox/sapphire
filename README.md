# Sapphire

A toy SSA-based compiler IR and optimizing middle/back-end.

## Examples

### Recursive Factorial

```c
int factorial(int x) {
  if (x < 2) {
    return 1;
  } 
  
  return x * factorial(x - 1);
}
```

```
def i32 @factorial(i32) {
entry(i32 %x):
  %0 = iconst i32 2
  %1 = icmp lt i32 %x, %0
  condbr bool %1, lessThanTwo, recurse

lessThanTwo:
  %2 = iconst i32 1
  br exit(i32 %2)

recurse:
  %3 = iconst i32 1
  %4 = isub i32 %x, %3
  %5 = call @factorial(i32 %4)
  %6 = imul i32 %x, %5
  br exit(i32 %6)
  
exit(i32 %result):
  ret i32 %result
}
```

### Iterative Fibonacci

```c 
int fibonacci(int x) {
  int a = 0;
  int b = 1;
  
  for (int i = 0; i < x; ++i) {
    int c = a + b;
    a = b;
    b = c;
  }
  
  return a;
}
```

```llvm
def i32 @fibonacci(i32) {
entry(i32 %0):
  %1 = iconst i32 0
  %2 = iconst i32 1
  br loop.head(i32 %1, i32 %1, i32 %2)
 
loop.head(i32 %i, i32 %a, i32 %b)
  %3 = icmp lt i32 %i, %0
  condbr bool %3, loop(i32 %a, i32 %b), exit(i32 %a)
 
loop(i32 %a, i32 %b):
  %4 = iadd i32 %i, %2
  %c = iadd i32 %a, %b
  br loop.head(i32 %4, i32 %b, i32 %c)

exit(i32 %a)
  ret i32 %a
}
```

