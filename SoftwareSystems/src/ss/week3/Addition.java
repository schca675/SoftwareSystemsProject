package ss.week3;

public class Addition implements OperatorWithIdentity {

	public int operate(int left, int right) {
		return left + right;
	}

	public int identity() {
		return 0;
	}

	public static void main(String[] args) {
		OperatorWithIdentity op = new Addition();
		System.out.println(op.operate(2, 3));
		OperatorWithIdentity op2 = new Multiplication();
		System.out.println(op2.operate(2, 3));
	}

}
