package ss.week3;

public class BasicChecker implements Checker {
	
	public static final String INITIAL = "zyxwvuts";

	public boolean acceptable(String password) {
		return password.length() >= 6 && !password.contains(" ");
	}

	public String generatePassword() {
		return INITIAL;
	}

}
