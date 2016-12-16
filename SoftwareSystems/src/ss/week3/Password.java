package ss.week3;

public class Password {
	private String password;
	private Checker checker;
	private String factoryPassword;
	private static final Checker DEFAULTCHECKER = new BasicChecker();

	public Password() {
		this(DEFAULTCHECKER);
	}

	public Password(Checker checker) {
		this.checker = checker;
		this.factoryPassword = checker.generatePassword();
		password = factoryPassword;
	}

	public boolean acceptable(String suggestion) {
		return checker.acceptable(suggestion);
	}

	public Checker getChecker() {
		return checker;
	}
	
	public String getFactoryPassword() {
		return factoryPassword;
	}

	// --------------- Last Week ----------------------

	/* @pure */ public boolean testWord(String test) {
		return password.equals(test);
	}

	public boolean setWord(String oldpass, String newpass) {
		if (!this.testWord(oldpass)) {
			return false;
		} else if (!this.acceptable(newpass)) {
			return false;
		} else {
			password = newpass;
			return true;
		}
	}

}
