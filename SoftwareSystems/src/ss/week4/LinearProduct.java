package ss.week4;

public class LinearProduct extends Product implements Integrandable {
	private Function function;
	private Constant constant;
	
	public LinearProduct(Function function, Constant constant) {
		super(function, constant);
		this.function = function;
		this.constant = constant;
	}
	
	@Override
	public Function derivative() {
		return new LinearProduct(function.derivative(), constant);
	}
	
	@Override
	public Function integrand() {
		if (function instanceof Integrandable) {
			return new LinearProduct(((Integrandable) function).integrand(), constant);
		} else {
			return null;
		}
	}
}
