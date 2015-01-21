package clientserver;

/**
 * Features class for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class Features {
	//PROTOCOL
	public static final String CHAT = "CHAT";
	public static final String LEADERBOARD = "LEADERBOARD";
	public static final String CUSTOM_BOARD_SIZE = "CUSTOM_BOARD_SIZE";
	public static final String SECURITY = "SECURITY";
	public static final String MULTIPLAYER = "MULTIPLAYER";
	public static final String[] FEATURES = new String[] { CHAT, LEADERBOARD,
			CUSTOM_BOARD_SIZE, SECURITY, MULTIPLAYER };
	//END OF PROTOCOL
}
