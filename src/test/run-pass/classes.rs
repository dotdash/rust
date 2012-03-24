class cat {
  priv {
    let mutable meows : uint;
    fn meow() {
      #error("Meow");
      meows += 1u;
      if meows % 5u == 0u {
          how_hungry += 1;
      }
    }
  }

  let how_hungry : int;

  new(in_x : uint, in_y : int) { meows = in_x; how_hungry = in_y; }

  fn speak() { meow(); }

  fn eat() -> bool {
    if how_hungry > 0 {
        #error("OM NOM NOM");
        how_hungry -= 2;
        ret true;
    }
    else {
        #error("Not hungry!");
        ret false;
    }
  }
}

fn main() {
  let nyan = cat(0u, 2);
  nyan.eat();
  assert(!nyan.eat());
  uint::range(1u, 10u, {|_i| nyan.speak(); });
  assert(nyan.eat());
}