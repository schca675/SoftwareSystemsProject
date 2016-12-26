package model;

public class Board {
	int xSize;
	int ySize;
	int zSize;
	int winningLength;
	int boardData[][][];
	
	//@ private invariant winningLength <= xSize || winningLength <= ySize || winningLength <= zSize
	//@ private invariant xSize > 0 && ySize > 0 && zSize > 0 && winningLength > 0
	
	/** Create a new board with specified dimensions and winning length
	 * @param xDim X dimension of the board
	 * @param yDim Y dimension of the board
	 * @param zDim Z dimension of the board
	 * @param winningLength Connected pieces required to win the game
	 */
	//@ requires lengthToWin <= xDim || winningLength <= yDim || winningLength <= zDim
	//@ requires xDim > 0 && yDim > 0 && zDim > 0 && lengthToWin > 0
	public Board(int xDim, int yDim, int zDim, int lengthToWin) {
		xSize = xDim;
		ySize = yDim;
		zSize = zDim;
		winningLength = lengthToWin;
		boardData = new int[xDim][yDim][zDim];
	}
	
	public int getCell(int x, int y, int z) {
		return boardData[x-1][y-1][z-1];
	}
	
	/** Checks whether a piece can be added to tower at (x,y)
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @return (x,y) is valid tower to add piece to
	 */
	//@ ensures \result == (isValidTower(x,y) && getTowerHeight(x,y) < sSize)
	public boolean checkMove(int x, int y) {
		return isExistingTower(x,y) && getTowerHeight(x,y) < zSize;
	}
	
	/** Make a move if it is valid
	 * 
	 * @param x X position to place piece at
	 * @param y Y position to place piece at
	 * @return Move has been made
	 */
	//@ ensures checkMove(x,y) ==> \result == true && getOwner(x,y,getTowerHeight(x,y)) == playerID
	//@ ensures !checkMove(x,y) ==> \result == false
	public boolean makeMove(int x, int y, int playerID) {
		if (!checkMove(x, y)) {
			return false;
		} else {
			int z = getTowerHeight(x, y);
			boardData[x-1][y-1][z-1] = playerID;
			return true;
		}
	}
	
	/** Returns the owner number of the cell, 0 if no owner
	 * 
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return Owner number, 0 if no owner
	 */
	//@ requires isExistingCell(x,y,z)
	//@ ensures \result = ?
	public int getCellOwner(int x, int y, int z) {
		return getCell(x, y, z);
	}
	
	/** Checks whether the given cell is empty
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @param z Z position to check
	 * @return (x,y,z) is empty
	 */
	//@ requires isExistingCell(x,y,z)
	//@ ensures \result == (getCellOwner(x,y,z) == 0)
	public boolean isEmptyCell(int x, int y, int z) {
		return (getCellOwner(x,y,z) == 0);
	}
	
	/** Checks whether the board is full
	 * 
	 * @return Board is full
	 */
	//@ ensures \result == (\forall int x,y,z; isExistingCell(x,y,z); !isEmptyCell(x,y,z))
	public boolean isFull() {
		return false;
	}
	
	/** Returns the height of the tower at (x,y)
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @return The height of the tower at (x,y)
	 */
	//@ requires isValidTower(x,y)
	//@ ensures \result == ?
	public int getTowerHeight(int x, int y) {
		return 0;
	}
	
	/** Checks whether the piece at (x,y,z) belongs to a winning set
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @param z Z position to check
	 * @return Piece at (x,y,z) belongs to winning set
	 */
	//@ requires isExistingCell(x,y,z)
	public boolean hasWon(int x, int y, int z) {
		return false;
	}
	
	/** Checks whether (x,y) is an existing tower on the board
	 * 
	 * @param x X position
	 * @param y Y position
	 * @return (x,y) are valid coordinates on the board
	 */
	//@ ensures \result == (x >= 0 && x <= xSize && y >= 0 && y <= ySize)
	public boolean isExistingTower(int x, int y) {
		return false;
	}
	
	/** Checks whether (x,y,z) is an existing cell on the board
	 * 
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return (x,y,z) are valid coordinates on the board
	 */
	//@ ensures \result == (isValidTower(x,y) && z >= 0 && z <= zSize)
	public boolean isExistingCell(int x, int y, int z) {
		return false;
	}

}
