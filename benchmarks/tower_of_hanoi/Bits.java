import tlc2.value.IntValue;

public class Bits {
    public static IntValue And(IntValue x, IntValue y) {
        return IntValue.gen(x.val & y.val);
    }
}

