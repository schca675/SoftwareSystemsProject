package ss.week2.hotel;

public class Password {
	public static final String INITIAL = "acdefghcudnfdj";
	private String password;

	public Password() {
		password = INITIAL;
	}

	public boolean acceptable(String suggestion) {
		if (suggestion.length() < 6 || suggestion.contains(" ")) {
			return false;
		} else {
			return true;
		}
	}

	/*@pure */ public boolean testWord(String test) {
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
