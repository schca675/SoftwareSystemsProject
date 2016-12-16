package ss.week1;

public class student{
	public static final int REQSCORE = 70;

	public boolean passed(int score) {
		return score >= REQSCORE;
	}

	public static void main(String[] args) {

		boolean test = 6 > 5;
		if (test) {
			System.out.println("ja");
		}

	}

}