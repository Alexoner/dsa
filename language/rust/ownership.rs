fn test_second_borrow() {
    let mut v = vec![1, 2, 3];
    for i in &mut v {
        println!("{}", i);
        v.ush(34); // second mutable borrow.
    }
}

fn main() {
    test_second_borrow();
}
