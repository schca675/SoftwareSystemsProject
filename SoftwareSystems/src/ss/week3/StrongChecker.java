package ss.week3;

public class StrongChecker extends BasicChecker {

	public static final String INITIALSTRONG = "wabcdeffc6";

	public boolean acceptable(String password) {
		char firstLetter = password.charAt(0);
		char lastLetter = password.charAt(password.length() - 1);
		boolean last = Character.isDigit(lastLetter);
		boolean first = Character.isLetter(firstLetter);
		boolean rightBounding = last && first;
		return super.acceptable(password) && rightBounding;
	}

	public String generatePassword() {
		return INITIALSTRONG;
	}

}
