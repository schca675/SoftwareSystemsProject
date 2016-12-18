package ss.week4;

public class Constant implements Function, Integrandable {
	private double value;

	public Constant(double constant) {
		value = constant;
	}
	
	@Override
	public double apply(double argument) {
		return value;
	}

	@Override
	public Function derivative() {
		return new Constant(0);
	}
	
	@Override
	public Function integrand() {
		return new LinearProduct(new Exponent(1), this);
	}
	
	@Override
	public String toString() {
		return "" + value;
	}
}