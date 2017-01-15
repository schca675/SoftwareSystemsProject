package model;

public class DummyException extends IllegalArgumentException {

	public String getMessage() {
		return "Congratulation, you got a dummy exception.";
	}
}
