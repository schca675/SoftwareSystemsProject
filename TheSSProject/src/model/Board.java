package model;

public class Board {
	private int winningLength;
	private int boardData[][][];
	
	/** Create a new board with specified dimensions and winning length
	 * @param xDim X dimension of the board
	 * @param yDim Y dimension of the board
	 * @param zDim Z dimension of the board
	 * @param lengthToWin Connected pieces required to win the game
	 */
	//@ requires lengthToWin <= xDim || lengthToWin <= yDim || lengthToWin <= zDim;
	//@ requires xDim > 0 && yDim > 0 && zDim > 0 && lengthToWin > 0;
	public Board(int xDim, int yDim, int zDim, int lengthToWin) {
		winningLength = lengthToWin;
		boardData = new int[xDim][yDim][zDim];
	}
	
	// <------ Queries ------>
	/** Getter for X dimension
	 * 
	 * @return X dimension
	 */
	/*@ pure */ public int getXDim() {
		return boardData.length;
	}

	/** Getter for Y dimension
	 * 
	 * @return Y dimension
	 */
	/*@ pure */ public int getYDim() {
		return boardData[0].length;
	}

	/** Getter for Z dimension
	 * 
	 * @return Z dimension
	 */
	/*@ pure */ public int getZDim() {
		return boardData[0][0].length;
	}

	/** Getter for cell
	 * 
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return Cell at (x,y,z)
	 */
	/*@ pure */ public int getCell(int x, int y, int z) {
		return boardData[x-1][y-1][z-1];
	}
	
	/** Checks whether a piece can be added to tower at (x,y)
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @return (x,y) is valid tower to add piece to
	 */
	//@ ensures \result == (isValidTower(x,y) && getTowerHeight(x,y) < getZDim());
	/*@ pure */ public boolean checkMove(int x, int y) {
		return isValidTower(x,y) && getTowerHeight(x,y) < getZDim();
	}
	
	/** Returns the owner number of the cell, 0 if no owner
	 * 
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return Owner number, 0 if no owner
	 */
	//@ requires isValidCell(x,y,z);
	// ensures \result = ?
	/*@ pure */ public int getCellOwner(int x, int y, int z) {
		return getCell(x, y, z);
	}
	
	/** Checks whether the given cell is empty
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @param z Z position to check
	 * @return (x,y,z) is empty
	 */
	//@ requires isValidCell(x,y,z);
	//@ ensures \result == (getCellOwner(x,y,z) == 0);
	/*@ pure */ public boolean isEmptyCell(int x, int y, int z) {
		return (getCellOwner(x,y,z) == 0);
	}
	
	/** Checks whether the board is full
	 * 
	 * @return Board is full
	 */
	//@ ensures \result == (\forall int x,y,z; isValidCell(x,y,z); !isEmptyCell(x,y,z));
	public boolean isFull() {
		return false;
	}
	
	/** Returns the height of the tower at (x,y)
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @return The height of the tower at (x,y)
	 */
	//@ requires isValidTower(x,y);
	// ensures \result == ?;
	/*@ pure */ public int getTowerHeight(int x, int y) {
		return 0;
	}
	
	/** Checks whether the piece at (x,y,z) belongs to a winning set
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @param z Z position to check
	 * @return Piece at (x,y,z) belongs to winning set
	 */
	//@ requires isValidCell(x,y,z);
	/*@ pure */ public boolean hasWon(int x, int y, int z) {
		return false;
	}
	
	/** Checks whether (x,y) is a valid tower on the board
	 * 
	 * @param x X position
	 * @param y Y position
	 * @return (x,y) are valid coordinates on the board
	 */
	//@ ensures \result == (x >= 0 && x <= getXDim() && y >= 0 && y <= getYDim());
	/*@ pure */ public boolean isValidTower(int x, int y) {
		return false;
	}
	
	/** Checks whether (x,y,z) is a valid cell on the board
	 * 
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return (x,y,z) are valid coordinates on the board
	 */
	//@ ensures \result == (isValidTower(x,y) && z >= 0 && z <= getZDim());
	/*@ pure */ public boolean isValidCell(int x, int y, int z) {
		return false;
	}
	
	// <----- Commands ----->
	
	/** Make a move if it is valid
	 * 
	 * @param x X position to place piece at
	 * @param y Y position to place piece at
	 * @param playerID ID of player that makes a move
	 * @return Move has been made
	 */
	//@ ensures checkMove(x,y) ==> \result == true && getCellOwner(x,y,getTowerHeight(x,y)) == playerID;
	//@ ensures !checkMove(x,y) ==> \result == false;
	public boolean makeMove(int x, int y, int playerID) {
		if (!checkMove(x, y)) {
			return false;
		} else {
			int z = getTowerHeight(x, y);
			boardData[x-1][y-1][z-1] = playerID;
			return true;
		}
	}

}
