package ss.week5;

import ss.week5.TicTacToe.Board;
import ss.week5.TicTacToe.Mark;

public class SmartStrategy implements Strategy {

	@Override
	public String getName() {
		return "Smart";
	}

	@Override
	public int determineMove(Board b, Mark m) {
		int dim = Board.DIM;
		// if middle field empty
		if (b.isEmptyField(dim * dim / 2)) {
			return dim * dim / 2;
		} else {
			// determining if the player can win in the next turn
			int i = 0;
			int meWinner = -1;
			boolean meWin = false;
			while (i < dim * dim && !meWin) {
				Board meTest = b.deepCopy();
				if (meTest.isEmptyField(i)) {
					meTest.setField(i, m);
					meWin = meTest.isWinner(m);
					if (meWin) {
						meWinner = i;
					}
				}
				i++;
			}
			// if yes, this field is taken
			if (meWin && meWinner >= 0) {
				return meWinner;
			} else {
				// determining if the opponent can win in the next turn
				int j = 0;
				int otherWinner = -1;
				boolean otherWin = false;
				while (j < dim * dim && !otherWin) {
					Board otherTest = b.deepCopy();
					if (otherTest.isEmptyField(j)) {
						otherTest.setField(j, m.other());
						otherWin = otherTest.isWinner(m.other());
						if (otherWin) {
							otherWinner = j;
						}
					}
					j++;
				}
				// if yes, this field is taken
				if (otherWin && otherWinner >= 0) {
					return otherWinner;				
				}
			}
		}
		// else a random field is selected.
		Strategy last = new NaiveStrategy();
		return last.determineMove(b, m);
	}

}
