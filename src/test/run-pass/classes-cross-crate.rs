// xfail-fast
// aux-build:cci_class_4.rs
use cci_class_4;
import cci_class_4::kitties::*;

fn main() {
  let nyan = cat(0u, 2);
  nyan.eat();
  assert(!nyan.eat());
  uint::range(1u, 10u, {|_i| nyan.speak(); });
  assert(nyan.eat());
}