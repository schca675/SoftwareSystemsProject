package ss.week4;

public class Constant implements Function {
	
	private double constant;
	
	public Constant(double value) {
		constant = value;
	}

	@Override
	public double apply(double argument) {
		return constant;
	}

	@Override
	public Function derivative() {
		return new Constant(0);
	}
	
	public String toString() {
		return "f(x) = " + constant;
	}

}
