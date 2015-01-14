package clientserver;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;

/**
 * P2 prac wk4. <br>
 * Client.
 * 
 * @author Theo Ruys
 * @version 2005.02.21
 */
public class Client extends Thread {
	// PROTOCOL
	public static final String CONNECT = "CONNECT";
	public static final String QUIT = "QUIT";
	public static final String INVITE = "INVITE";
	public static final String ACCEPT_INVITE = "ACCEPT";
	public static final String DECLINE_INVITE = "DECLINE";
	public static final String MOVE = "MOVE";
	public static final String CHAT = "CHAT";
	public static final String REQUEST_BOARD = "REQUEST";
	public static final String REQUEST_LOBBY = "LOBBY";
	public static final String REQUEST_LEADERBOARD = "LEADERBOARD";
	// END OF PROTOCOL
	private String clientName;
	private MessageUI mui;
	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	private boolean loop;

	/**
	 * Constructs a Client-object and tries to make a socket connection
	 */
	public Client(String name, InetAddress host, int port, MessageUI muiArg)
			throws IOException {
		this.clientName = name;
		this.sock = new Socket(host, port);
		this.mui = muiArg;
		this.in = new BufferedReader(new InputStreamReader(
				sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(
				sock.getOutputStream()));
		this.loop = true;
	}

	/**
	 * Reads the messages in the socket connection. Each message will be
	 * forwarded to the MessageUI
	 */

	public void run() {
		sendMessage(getClientName());
		// PROTOCOLTEST
		sendMessage("Client: " + CONNECT + " " + getClientName()
				+ " Feature1 Feature2 Feature3 Feature4");
		sendMessage("Server: " + Server.ACCEPT_CONNECT
				+ " ServerFeature1 ServerFeature2" + " (of " + Server.ERROR
				+ ")");
		sendMessage("Client: " + REQUEST_LOBBY);
		sendMessage("Server: " + Server.LOBBY + " Michael Sven Kip Haan");
		sendMessage("Client: " + INVITE + " Naam");
		sendMessage("Server: " + Server.INVITE + " Naam");
		sendMessage("Client2: " + ACCEPT_INVITE + " (of " + DECLINE_INVITE
				+ ")");
		sendMessage("Server: " + Server.GAME_START);
		sendMessage("Loop:");
		sendMessage("Server: " + Server.REQUEST_MOVE + " (naar client1)");
		sendMessage("Client: " + MOVE + " move_getal");
		sendMessage("Server: " + Server.MOVE_OK + " (of " + Server.ERROR + "?)");
		sendMessage("Server: " + "Stuur naar client2 welke move is gedaan.");
		sendMessage("Server: " + Server.REQUEST_MOVE+ " (naar client2uj)");
		sendMessage("Client2: " + MOVE + " move_getal");
		sendMessage("Server: " + Server.MOVE_OK + " (of " + Server.ERROR + "?)");
		sendMessage("Server: " + "Stuur naar client1 welke move is gedaan.");
		sendMessage("End loop.");
		sendMessage("Server: " + Server.GAME_END);
		// END PROTOCOLTEST
		while (loop) {
			try {
				String message = in.readLine();
				if (message != null) {
					if ("EXIT".equals(message)) {
						shutdown();
					}
					mui.addMessage(message);
				}
			} catch (IOException ex) {
				shutdown();
			}
		}
	}

	/** send a message to a ClientHandler. */
	public void sendMessage(String msg) {
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
	}

	/** close the socket connection. */
	public void shutdown() {
		loop = false;
		try {
			sock.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		System.exit(0);
	}

	/** returns the client name */
	public String getClientName() {
		return clientName;
	}

} // end of class Client
